#include <jalv_internal.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/un.h>
#include <unistd.h>
#include <sys/select.h>
#include <stdio.h>
#include <ctype.h>
#include "lilv/lilv.h"


static int sockfd = -1, connfd = -1, newconnfd;
static struct sockaddr_un server_un;
static ZixThread server_thread, conn_thread;
static uint32_t exit_requested;

// b64 encoding avoiding special OSC chars.
static char encode_table[] =
"ABCDEFGHIJKLMNOPQRSTUVWXYZ"
"abcdefghijklmnopqrstuvwxyz"
"0123456789"
"+/";

static uint32_t decode_table[128];

static __attribute__((constructor)) void build_b64_decode_table()
{
    int i = 0;

    for (i = 63; i >= 0; i--)
        decode_table[encode_table[i]] = i;
}

struct __attribute__ ((packed)) b64template {
    float current;
    uint16_t index;
    float minimum;
    float maximum;
    uint8_t pad;
};

#define TEMPLATE_END ((sizeof(struct b64template)+2)/3 * 4)

static void encode_template(struct b64template *tpl, char *dst)
{
    uint8_t *src = (uint8_t *)tpl;
    
    for (int i=0; i < sizeof(*tpl); i+=3, src += 3) {
	uint32_t q = src[2] | (src[1] | (src[0] << 8)) << 8;
	*dst++ = encode_table[q >> 18];
	*dst++ = encode_table[q >> 12 & 63];
	*dst++ = encode_table[q >> 6 & 63];
	*dst++ = encode_table[q & 63];
    }
}

static void decode_setter(char *input, uint16_t *index, float *value)
{
    struct parts {
	float value;
	uint16_t param;
    } parmspec;

    uint8_t *pun = (uint8_t *)&parmspec, *src = input;
    uint32_t q = decode_table[src[3]] |
        (decode_table[src[2]] |
         (decode_table[src[1]] |
          decode_table[src[0]] << 6) << 6) << 6;
    pun[0] = q >> 16;
    pun[1] = q >> 8 & 0xff;
    pun[2] = q & 0xff;
    q = decode_table[src[7]] |
        (decode_table[src[6]] |
         (decode_table[src[5]] |
          decode_table[src[4]] << 6) << 6) << 6;
    pun[3] = q >> 16;
    pun[4] = q >> 8 & 0xff;
    pun[5] = q & 0xff;
    *index = parmspec.param;
    *value = parmspec.value;
}

static void* show_controls_b64(Jalv *jalv, int fd, bool show_limits)
{
    char out[TEMPLATE_END + 1];
    out[TEMPLATE_END] = 0;

    for (int ix = 0; ix < jalv->num_ports; ix++) {
	struct Port* const port = &jalv->ports[ix];
	if (port->type != TYPE_CONTROL)
	    continue;
		    
	const LilvNode* sym =
	    lilv_port_get_symbol(jalv->plugin,
				 port->lilv_port);

	struct b64template tmpl = { port->control, ix, 0, 0, 0};

	if (show_limits) {
	    LilvNode *dflt, *min, *max;
	    lilv_port_get_range(jalv->plugin, port->lilv_port,
				&dflt, &min, &max);
	    tmpl.minimum = lilv_node_as_float(min);
	    tmpl.maximum = lilv_node_as_float(max);
	    lilv_node_free(dflt);
	    lilv_node_free(min);
	    lilv_node_free(max);
	}

	encode_template(&tmpl, out);

	if (show_limits)
	    dprintf(fd, "%.8s %s %s\n", out, &out[8],
		    lilv_node_as_string(sym));
	else
	    dprintf(fd, "%.8s %s\n", out, lilv_node_as_string(sym));
    }
}

static void* show_controls(Jalv *jalv, int fd, bool raw)
{
    for (int ix = 0; ix < jalv->num_ports; ix++) {
	struct Port* const port = &jalv->ports[ix];
	if (port->type != TYPE_CONTROL)
	    continue;
	const LilvNode* sym = lilv_port_get_symbol(jalv->plugin,
						   port->lilv_port);
	if (raw)
	    dprintf(fd, "%d:%s = 0x%X\n", ix, lilv_node_as_string(sym),
		    *(uint32_t *)&port->control);
	else
	    dprintf(fd, "%d:%s = %f\n", ix, lilv_node_as_string(sym),
		    port->control);
    }
    if (!raw)
	dprintf(fd, "##\n");
}

#define WAIT_MICROSEC 25000

static enum {
    THR_NONE,
    THR_RUNNING,
    THR_EXIT
} thread_state;

static char *nexttoken(char **str)
{
    char *cursor = *str;
    while (isspace(*cursor)) cursor++;
    if (!*cursor) return NULL;

    enum { qnormal, qbackslash, qoctal } state = qnormal;
    char *out = *str;
    char *tokstart = *str;
    char ch;
    char accum;
    int octct;

    while (ch = *cursor++) {
	switch (state) {
	case qnormal:
	    if (ch == '\\') {
		state = qbackslash;
		continue;
	    }
	    if (isspace(ch)) {
		*str = cursor;
		*out = 0;
		return tokstart;
	    }
	    *out++ = ch;
	    continue;
	case qbackslash:
	    switch (ch) {
	    case 'n': ch = '\n'; break;
	    case 'r': ch = '\r'; break;
	    case 't': ch = '\t'; break;
	    case 'v': ch = '\v'; break;
	    case 'f': ch = '\f'; break;
	    default:
		if (ch >= '0' && ch <= '7') {
		    state = qoctal;
		    accum = ch-'0';
		    octct = 1;
		    continue;
		}
	    }
	    *out++ = ch;
	    state = qnormal;
	    continue;
	case qoctal:
	    if (ch < '0' || ch > '7' || octct == 3) {
		*out++ = accum;
		cursor--;
		state = qnormal;
	    } else {
		accum = accum<<3 | ch-'0';
		octct++;
	    }
	}
    }
    if (state == qoctal)
	*out++ = accum;
    *str = cursor - 1;
    *out = 0;
    return tokstart != out ? tokstart : NULL;
}

static LilvNode *preset;

static int load_preset_by_title(Jalv*           jalv,
				const LilvNode* node,
				const LilvNode* title,
				void*           sought)
{
    if (!strcmp(sought, lilv_node_as_string(title)))
	preset = lilv_new_uri(jalv->world,
			      lilv_node_as_string(node));
}

static void load_preset_or_state(Jalv * jalv, char *preset_name)
{
    LilvState * state      = NULL;
    if (*preset_name != '/') {
	jalv_unload_presets(jalv);
	jalv_load_presets(jalv, load_preset_by_title, preset_name);
	if (preset) {
	    state = lilv_state_new_from_world(jalv->world, &jalv->map, preset);
	    lilv_node_free(preset);
	    preset = NULL;
	}
    } else {
	char * path = jalv_strjoin(preset_name, "/state.ttl");
	state = lilv_state_new_from_file(jalv->world, &jalv->map, NULL,
					 path);
	free(path);
    }
    if (state) {
	if (jalv->preset)
	    lilv_state_free(jalv->preset);
	jalv->preset = state;
	jalv_apply_state(jalv, state);
    }
}

static void do_command(Jalv *jalv, char *cmdstr)
{
    char *p = cmdstr;
    char *token;
    char *cmdtok = "";
    char *param = "";
    char *param2 = "";

    if (token = nexttoken(&p)) {
	cmdtok = token;
	if (token = nexttoken(&p)) {
	    param = token;
	    if (token = nexttoken(&p))
		param2 = token;
	}
    }

    if (cmdtok[0] == '#') {
	show_controls_b64(jalv, connfd, cmdtok[1] == '#');
	dprintf(connfd, "##\n");
    } else if (cmdtok[0] == '<') {
	load_preset_or_state(jalv, param);
    } else if (cmdtok[0] == ':' && strlen(cmdtok) == 9) {
	uint16_t portno;
	float value;
	decode_setter(&cmdtok[1], &portno, &value);
	if (portno < jalv->num_ports) {
	    struct Port* const port = &jalv->ports[portno];
	    if (port->type = TYPE_CONTROL)
		port->control = value;
	}
    } else if (!strcmp(cmdtok, "list_params")) {
	show_controls(jalv, connfd, param[0]);
    } else
	dprintf(connfd, "<FAIL>\n");
}

#define BUFSIZE 1024

static void* conn_func(void *data)
{
    Jalv *jalv = (Jalv *)data;
    char buf[BUFSIZE+1], *base = buf;
    bool skipping = false;
    int nextix = 0;
    while (!exit_requested) {
	fd_set read_set;
	FD_ZERO(&read_set);
	FD_SET(connfd, &read_set);
	struct timeval timeout = { 0, WAIT_MICROSEC };
        if (select(connfd+1, &read_set, NULL, NULL, &timeout) > 0) {
	    int actual = read(connfd, base + nextix, BUFSIZE - nextix);
	    if (actual < 1)
		goto bugout;
	    nextix += actual;
	    char *start = base;
	    bool newline_seen = false;
	    char *end;
	        while (end = strchr(start, '\n')) {
		    newline_seen = true;
		    if (!skipping) {
			*end = 0;
			do_command(jalv, start);
		    } else
			skipping = false;
		    start = end + 1;
		}
		if (newline_seen) {
		    nextix -= (start - base);
		    memmove(base, start, nextix);
		} else if (nextix == BUFSIZE) {
		    skipping = true;
		    nextix = 0;
		}
	}
    }
bugout:
    close(connfd);
    thread_state = THR_EXIT;
    return NULL;
}

static void * server_func(void *data)
{
    Jalv *jalv = (Jalv *)data;
    
    while (!exit_requested) {
	fd_set read_set;
	FD_ZERO(&read_set);
	FD_SET(sockfd, &read_set);
	struct timeval timeout = { 0, WAIT_MICROSEC };

        if (select(sockfd+1, &read_set, NULL, NULL, &timeout) > 0) {
	    newconnfd = accept(sockfd, NULL, 0);
	    if (thread_state == THR_RUNNING)
		close(newconnfd);
	    else {
		if (thread_state == THR_EXIT) {
		    zix_thread_join(conn_thread, NULL);
		}
		connfd = newconnfd;
		thread_state =
		    (zix_thread_create(&conn_thread, 4096, conn_func, jalv) ==
		     ZIX_STATUS_SUCCESS) ? THR_RUNNING : THR_NONE;
	    }
	}
    }

    if (thread_state != THR_NONE)
	zix_thread_join(conn_thread, NULL);
    
    return NULL;
}

int jalv_socket_init(Jalv *jalv)
{
    sockfd = socket(AF_UNIX , SOCK_STREAM , 0);
    if (sockfd >= 0) {
	socklen_t addrlen = strlen(jalv->opts.sockname);
	if (addrlen > sizeof(server_un.sun_path))
	    addrlen = sizeof(server_un.sun_path) - 1;
	memcpy(server_un.sun_path, jalv->opts.sockname, addrlen);
	server_un.sun_family = AF_UNIX;
	unlink(server_un.sun_path);
	if (bind(sockfd, (struct sockaddr *)&server_un,
		 sizeof(server_un)) >= 0 &&
	    listen(sockfd, 1) >= 0) {
	    if (zix_thread_create(&server_thread, 4096, server_func, jalv) ==
		ZIX_STATUS_SUCCESS)
		return 0;
	}
    }

    if (sockfd > 0)
	close(sockfd);
    unlink(server_un.sun_path);
    return -1;
}

void jalv_socket_finish(Jalv *jalv)
{
    exit_requested = 1;
    zix_thread_join(server_thread, NULL);
    if (sockfd)
	close(sockfd);
    unlink(jalv->opts.sockname);
    return;
}
