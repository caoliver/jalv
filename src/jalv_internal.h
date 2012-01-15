/*
  Copyright 2007-2011 David Robillard <http://drobilla.net>

  Permission to use, copy, modify, and/or distribute this software for any
  purpose with or without fee is hereby granted, provided that the above
  copyright notice and this permission notice appear in all copies.

  THIS SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
*/

#ifndef JALV_INTERNAL_H
#define JALV_INTERNAL_H

#include <semaphore.h>
#include <stdlib.h>
#include <string.h>

#include <jack/jack.h>
#include <jack/ringbuffer.h>

#include "lilv/lilv.h"
#include "serd/serd.h"
#include "suil/suil.h"

#include "lv2/lv2plug.in/ns/ext/urid/urid.h"
#include "lv2/lv2plug.in/ns/ext/state/state.h"

#include "lv2_evbuf.h"
#include "symap.h"

#ifdef __cplusplus
extern "C" {
#endif

#define JALV_UI_UPDATE_HZ 15

enum PortFlow {
	FLOW_UNKNOWN,
	FLOW_INPUT,
	FLOW_OUTPUT
};

enum PortType {
	TYPE_UNKNOWN,
	TYPE_CONTROL,
	TYPE_AUDIO,
	TYPE_EVENT
};

struct Port {
	const LilvPort*   lilv_port;
	enum PortType     type;
	enum PortFlow     flow;
	jack_port_t*      jack_port;  ///< For audio/MIDI ports, otherwise NULL
	LV2_Evbuf*        evbuf;      ///< For MIDI ports, otherwise NULL
	uint32_t          index;      ///< Port index
	float             control;    ///< For control ports, otherwise 0.0f
	bool              old_api;    ///< True for event, false for atom
};

/**
   Control change event, sent through ring buffers for UI updates.
*/
typedef struct {
	uint32_t index;
	uint32_t protocol;
	uint32_t size;
	uint8_t  body[];
} ControlChange;

typedef struct {
	char* uuid;
	char* load;
} JalvOptions;

typedef enum {
	JALV_RUNNING,
	JALV_PAUSE_REQUESTED,
	JALV_PAUSED
} JalvPlayState;

typedef struct {
	JalvOptions        opts;           ///< Command-line options
	const char*        prog_name;      ///< Program name (argv[0])
	LilvWorld*         world;          ///< Lilv World
	int                ui_width;       ///< Requested UI width
	int                ui_height;      ///< Requested UI height
	LV2_URID_Map       map;            ///< URI => Int map
	LV2_URID_Unmap     unmap;          ///< Int => URI map
	Symap*             symap;          ///< Symbol (URI) map
	jack_client_t*     jack_client;    ///< Jack client
	jack_ringbuffer_t* ui_events;      ///< Port events from UI
	jack_ringbuffer_t* plugin_events;  ///< Port events from plugin
	sem_t*             done;           ///< Exit semaphore
	sem_t              paused;         ///< Paused signal from process thread
	JalvPlayState      play_state;     ///< Current play state
	char*              temp_dir;       ///< Temporary plugin state directory
	char*              save_dir;       ///< Plugin save directory
	const LilvPlugin*  plugin;         ///< Plugin class (RDF data)
	const LilvUI*      ui;             ///< Plugin UI (RDF data)
	LilvInstance*      instance;       ///< Plugin instance (shared library)
	SuilInstance*      ui_instance;    ///< Plugin UI instance (shared library)
	void*              window;         ///< Window (if applicable)
	struct Port*       ports;          ///< Port array of size num_ports
	size_t             midi_buf_size;  ///< Size of MIDI port buffers
	uint32_t           num_ports;      ///< Size of the two following arrays:
	uint32_t           longest_sym;    ///< Longest port symbol
	jack_nframes_t     sample_rate;    ///< Sample rate
	jack_nframes_t     event_delta_t;  ///< Frames since last update sent to UI
	LilvNode*          input_class;    ///< Input port class (URI)
	LilvNode*          output_class;   ///< Output port class (URI)
	LilvNode*          control_class;  ///< Control port class (URI)
	LilvNode*          audio_class;    ///< Audio port class (URI)
	LilvNode*          event_class;    ///< Event port class (URI)
	LilvNode*          aevent_class;   ///< Atom event port class (URI)
	LilvNode*          midi_class;     ///< MIDI event class (URI)
	LilvNode*          preset_class;   ///< Preset class (URI)
	LilvNode*          label_pred;     ///< rdfs:label
	LilvNode*          optional;       ///< lv2:connectionOptional port property
	uint32_t           midi_event_id;  ///< MIDI event class ID
	uint32_t           atom_prot_id;   ///< Atom protocol ID
	bool               buf_size_set;   ///< True iff buffer size callback fired
} Jalv;

int
jalv_init(int* argc, char*** argv, JalvOptions* opts);

void
jalv_create_ports(Jalv* jalv);

struct Port*
jalv_port_by_symbol(Jalv* jalv, const char* sym);

LilvNode*
jalv_native_ui_type(Jalv* jalv);

int
jalv_open_ui(Jalv*         jalv,
             SuilInstance* instance);

void
jalv_ui_write(SuilController controller,
              uint32_t       port_index,
              uint32_t       buffer_size,
              uint32_t       protocol,
              const void*    buffer);

bool
jalv_emit_ui_events(Jalv* jalv);

int
jalv_ui_resize(Jalv* jalv, int width, int height);

typedef int (*PresetSink)(Jalv*           jalv,
                          const LilvNode* node,
                          const LilvNode* title,
                          void*           data);

int
jalv_load_presets(Jalv* jalv, PresetSink sink, void* data);

int
jalv_apply_preset(Jalv* jalv, const LilvNode* preset);

int
jalv_save_preset(Jalv* jalv, const char* label);

void
jalv_save(Jalv* jalv, const char* dir);

void
jalv_save_port_values(Jalv*           jalv,
                      SerdWriter*     writer,
                      const SerdNode* subject);
char*
jalv_make_path(LV2_State_Make_Path_Handle handle,
               const char*                path);

void
jalv_apply_state(Jalv* jalv, LilvState* state);

static inline char*
jalv_strdup(const char* str)
{
	const size_t len  = strlen(str);
	char*        copy = (char*)malloc(len + 1);
	memcpy(copy, str, len + 1);
	return copy;
}

static inline char*
jalv_strjoin(const char* a, const char* b)
{
	const size_t a_len = strlen(a);
	const size_t b_len = strlen(b);
	char* const  out   = (char*)malloc(a_len + b_len + 1);

	memcpy(out,         a, a_len);
	memcpy(out + a_len, b, b_len);
	out[a_len + b_len] = '\0';

	return out;
}

#ifdef __cplusplus
}  // extern "C"
#endif

#endif  // JALV_INTERNAL_H
