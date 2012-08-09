/*
  Copyright 2007-2012 David Robillard <http://drobilla.net>

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

#include <math.h>

#include <gtk/gtk.h>

#include "lv2/lv2plug.in/ns/ext/port-props/port-props.h"

#include "jalv_internal.h"

static GtkWidget*
new_box(gboolean horizontal, gint spacing)
{
	#if GTK_MAJOR_VERSION == 3
	return gtk_box_new(
		horizontal ? GTK_ORIENTATION_HORIZONTAL : GTK_ORIENTATION_VERTICAL,
		spacing);
	#else
	return (horizontal
	        ? gtk_hbox_new(FALSE, spacing)
	        : gtk_vbox_new(FALSE, spacing));
	#endif
}

static GtkWidget*
new_hscale(gdouble min, gdouble max, gdouble step)
{
	#if GTK_MAJOR_VERSION == 3
	return gtk_scale_new_with_range(GTK_ORIENTATION_HORIZONTAL, min, max, step);
	#else
	return gtk_hscale_new_with_range(min, max, step);
	#endif
}

static void
size_request(GtkWidget* widget, GtkRequisition* req)
{
	#if GTK_MAJOR_VERSION == 3
	gtk_widget_get_preferred_size(widget, NULL, req);
	#else
	gtk_widget_size_request(widget, req);
	#endif
}

static void
on_window_destroy(GtkWidget* widget,
                  gpointer   data)
{
	Jalv* jalv = (Jalv*)data;
	suil_instance_free(jalv->ui_instance);
	jalv->ui_instance = NULL;
	gtk_main_quit();
}

int
jalv_init(int* argc, char*** argv, JalvOptions* opts)
{
	GOptionEntry entries[] = {
		{ "uuid", 'u', 0, G_OPTION_ARG_STRING, &opts->uuid,
		  "UUID for Jack session restoration", "UUID" },
		{ "load", 'l', 0, G_OPTION_ARG_STRING, &opts->load,
		  "Load state from save directory", "DIR" },
		{ "dump", 'd', 0, G_OPTION_ARG_NONE, &opts->dump,
		  "Dump plugin <=> UI communication", NULL },
		{ "generic-ui", 'g', 0, G_OPTION_ARG_NONE, &opts->generic_ui,
		  "Use Jalv generic UI and not the plugin UI", NULL},
		{ "buffer-size", 'b', 0, G_OPTION_ARG_INT, &opts->buffer_size,
		  "Buffer size for plugin <=> UI communication", "SIZE"},
		{ 0, 0, 0, 0, 0, 0, 0 } };
	GError* error = NULL;
	const int err = gtk_init_with_args(
		argc, argv,
		"PLUGIN_URI - Run an LV2 plugin as a Jack application",
		entries, NULL, &error);

	if (!err) {
		fprintf(stderr, "%s\n", error->message);
	}

	return !err;
}

const char*
jalv_native_ui_type(Jalv* jalv)
{
#if GTK_MAJOR_VERSION == 2
	return "http://lv2plug.in/ns/extensions/ui#GtkUI";
#elif GTK_MAJOR_VERSION == 3 
	return "http://lv2plug.in/ns/extensions/ui#Gtk3UI";
#else
	return NULL;
#endif
}

static void
on_save_activate(GtkWidget* widget, void* ptr)
{
	Jalv* jalv = (Jalv*)ptr;
	GtkWidget* dialog = gtk_file_chooser_dialog_new(
		"Save State",
		jalv->window,
		GTK_FILE_CHOOSER_ACTION_CREATE_FOLDER,
		GTK_STOCK_CANCEL, GTK_RESPONSE_CANCEL,
		GTK_STOCK_SAVE, GTK_RESPONSE_ACCEPT,
		NULL);

	if (gtk_dialog_run(GTK_DIALOG(dialog)) == GTK_RESPONSE_ACCEPT) {
		char* path = gtk_file_chooser_get_filename(GTK_FILE_CHOOSER(dialog));
		char* base = g_build_filename(path, "/", NULL);
		jalv_save(jalv, base);
		g_free(path);
		g_free(base);
	}

	gtk_widget_destroy(dialog);
}

static void
on_quit_activate(GtkWidget* widget, gpointer data)
{
	GtkWidget* window = (GtkWidget*)data;
	gtk_widget_destroy(window);
}

typedef struct {
	Jalv*     jalv;
	LilvNode* preset;
} PresetRecord;

static char*
symbolify(const char* in)
{
	const size_t len = strlen(in);
	char*        out = calloc(len + 1, 1);
	for (size_t i = 0; i < len; ++i) {
		if (g_ascii_isalnum(in[i])) {
			out[i] = in[i];
		} else {
			out[i] = '_';
		}
	}
	return out;
}

static void
on_save_preset_activate(GtkWidget* widget, void* ptr)
{
	Jalv* jalv = (Jalv*)ptr;

	GtkWidget* dialog = gtk_file_chooser_dialog_new(
		"Save Preset",
		jalv->window,
		GTK_FILE_CHOOSER_ACTION_SAVE,
		GTK_STOCK_CANCEL, GTK_RESPONSE_REJECT,
		GTK_STOCK_SAVE, GTK_RESPONSE_ACCEPT,
		NULL);

	char* dot_lv2 = g_build_filename(g_get_home_dir(), ".lv2", NULL);
	gtk_file_chooser_set_current_folder(GTK_FILE_CHOOSER(dialog), dot_lv2);
	free(dot_lv2);

	GtkWidget* content   = gtk_dialog_get_content_area(GTK_DIALOG(dialog));
	GtkBox*    box       = GTK_BOX(new_box(true, 8));
	GtkWidget* uri_label = gtk_label_new("URI (Optional):");
	GtkWidget* uri_entry = gtk_entry_new();

	gtk_box_pack_start(box, uri_label, FALSE, TRUE, 2);
	gtk_box_pack_start(box, uri_entry, TRUE, TRUE, 2);
	gtk_box_pack_start(GTK_BOX(content), GTK_WIDGET(box), FALSE, FALSE, 6);

	gtk_widget_show_all(GTK_WIDGET(dialog));
	gtk_entry_set_activates_default(GTK_ENTRY(uri_entry), TRUE);
	gtk_dialog_set_default_response(GTK_DIALOG(dialog), GTK_RESPONSE_ACCEPT);
	if (gtk_dialog_run(GTK_DIALOG(dialog)) == GTK_RESPONSE_ACCEPT) {
		const char* path = gtk_file_chooser_get_filename(GTK_FILE_CHOOSER(dialog));
		const char* uri  = gtk_entry_get_text(GTK_ENTRY(uri_entry));

		char* dirname  = g_path_get_dirname(path);
		char* basename = g_path_get_basename(path);
		char* sym      = symbolify(basename);
		char* bundle   = g_strjoin(NULL, sym, ".lv2", NULL);
		char* file     = g_strjoin(NULL, sym, ".ttl", NULL);
		char* dir      = g_build_filename(dirname, bundle, NULL);

		jalv_save_preset(jalv, dir, (strlen(uri) ? uri : NULL), basename, file);

		g_free(dir);
		g_free(file);
		g_free(bundle);
		free(sym);
		g_free(basename);
		g_free(dirname);
	}

	gtk_widget_destroy(GTK_WIDGET(dialog));
}

static void
on_preset_activate(GtkWidget* widget, gpointer data)
{
	PresetRecord* record = (PresetRecord*)data;
	jalv_apply_preset(record->jalv, record->preset);
}

static void
on_preset_destroy(gpointer data, GClosure* closure)
{
	PresetRecord* record = (PresetRecord*)data;
	lilv_node_free(record->preset);
	free(record);
}

static int
add_preset_to_menu(Jalv*           jalv,
                   const LilvNode* node,
                   const LilvNode* title,
                   void*           data)
{
	GtkWidget*  presets_menu = GTK_WIDGET(data);
	const char* label        = lilv_node_as_string(title);
	GtkWidget*  item         = gtk_menu_item_new_with_label(label);

	PresetRecord* record = (PresetRecord*)malloc(sizeof(PresetRecord));
	record->jalv   = jalv;
	record->preset = lilv_node_duplicate(node);

	g_signal_connect_data(G_OBJECT(item), "activate",
	                      G_CALLBACK(on_preset_activate),
	                      record, on_preset_destroy,
	                      0);

	gtk_menu_shell_append(GTK_MENU_SHELL(presets_menu), item);
	return 0;
}

void
jalv_ui_port_event(Jalv*       jalv,
                   uint32_t    port_index,
                   uint32_t    buffer_size,
                   uint32_t    protocol,
                   const void* buffer)
{
	GtkWidget* widget = jalv->ports[port_index].widget;
	if (!widget) {
		return;
	}

	if (GTK_IS_COMBO_BOX(widget)) {
		GtkTreeModel* model = gtk_combo_box_get_model(GTK_COMBO_BOX(widget));
		GValue        value = { 0, { { 0 } } };
		GtkTreeIter   i;
		bool          valid = gtk_tree_model_get_iter_first(model, &i);
		while (valid) {
			gtk_tree_model_get_value(model, &i, 0, &value);
			const double v = g_value_get_double(&value);
			g_value_unset(&value);
			if (fabs(v - *(float*)buffer) < FLT_EPSILON) {
				gtk_combo_box_set_active_iter(GTK_COMBO_BOX(widget), &i);
				return;
			}
			valid = gtk_tree_model_iter_next(model, &i);
		}
	} else if (GTK_IS_TOGGLE_BUTTON(widget)) {
		gtk_toggle_button_set_active(GTK_TOGGLE_BUTTON(widget),
		                             *(float*)buffer > 0.0f);
	} else if (GTK_IS_RANGE(widget)) {
		gtk_range_set_value(GTK_RANGE(widget), *(float*)buffer);
	} else {
		fprintf(stderr, "Unknown widget type for port %d\n", port_index);
	}
}

static gboolean
slider_changed(GtkRange* range, gpointer data)
{
	((struct Port*)data)->control = gtk_range_get_value(range);
	return FALSE;
}

static gboolean
log_slider_changed(GtkRange* range, gpointer data)
{
	((struct Port*)data)->control = expf(gtk_range_get_value(range));
	return FALSE;
}

static void
combo_changed(GtkComboBox* box, gpointer data)
{
	GtkTreeIter iter;
	if (gtk_combo_box_get_active_iter(box, &iter)) {
		GtkTreeModel* model = gtk_combo_box_get_model(box);
		GValue        value = { 0, { { 0 } } };

		gtk_tree_model_get_value(model, &iter, 0, &value);
		const double v = g_value_get_double(&value);
		g_value_unset(&value);

		((struct Port*)data)->control = v;
	}
}

static gboolean
toggle_changed(GtkToggleButton* button, gpointer data)
{
	float fval = gtk_toggle_button_get_active(button) ? 1.0f : 0.0f;
	((struct Port*)data)->control = fval;
	return FALSE;
}

static gchar*
scale_format(GtkScale* scale, gdouble value, gpointer user_data)
{
	gpointer hval = g_hash_table_lookup(user_data, &value);
	return hval ? g_strdup(hval) :
		g_strdup_printf("%0.*f", gtk_scale_get_digits(scale), value);
}

static gchar*
log_scale_format(GtkScale* scale, gdouble value, gpointer user_data)
{
	return g_strdup_printf("%0.6g", exp(gtk_range_get_value(GTK_RANGE(scale))));
}

static gint
dcmp(gconstpointer a, gconstpointer b)
{
	double y = *(double*)a;
	double z = *(double*)b;
	return y < z ? -1 : z < y ? 1 : 0;
}

static GtkWidget*
make_combo(struct Port* port, GHashTable* points, int deft)
{
	GList*        list       = g_hash_table_get_keys(points);
	GtkListStore* list_store = gtk_list_store_new(
		2, G_TYPE_DOUBLE, G_TYPE_STRING);
	for (GList* cur = g_list_sort(list, dcmp); cur; cur = cur->next) {
		GtkTreeIter iter;
		gtk_list_store_append(list_store, &iter);
		gtk_list_store_set(list_store, &iter,
		                   0, *(double*)cur->data,
		                   1, g_hash_table_lookup(points, cur->data),
		                   -1);
	}
	g_list_free(list);

	GtkWidget* combo = gtk_combo_box_new_with_model(GTK_TREE_MODEL(list_store));
	gtk_combo_box_set_active(GTK_COMBO_BOX(combo), deft);
	g_object_unref(list_store);

	GtkCellRenderer* cell = gtk_cell_renderer_text_new();
	gtk_cell_layout_pack_start(GTK_CELL_LAYOUT(combo), cell, TRUE);
	gtk_cell_layout_set_attributes(GTK_CELL_LAYOUT(combo), cell, "text", 1, NULL);

	g_signal_connect(G_OBJECT(combo),
	                 "changed", G_CALLBACK(combo_changed), port);

	return combo;
}

static GtkWidget*
make_log_slider(struct Port* port, GHashTable* points,
                float min, float max, float deft)
{
	float      lmin   = logf(min);
	float      lmax   = logf(max);
	float      ldft   = logf(deft);
	GtkWidget* slider = new_hscale(lmin, lmax, 0.001);
	gtk_scale_set_digits(GTK_SCALE(slider), 6);
	gtk_range_set_value(GTK_RANGE(slider), ldft);
	g_signal_connect(G_OBJECT(slider),
	                 "format-value", G_CALLBACK(log_scale_format), points);
	g_signal_connect(G_OBJECT(slider),
	                 "value-changed", G_CALLBACK(log_slider_changed), port);

	return slider;
}

static GtkWidget*
make_slider(struct Port* port, GHashTable* points,
            bool is_int, float min, float max, float deft)
{
	const double step   = is_int ? 1.0 : ((max - min) / 100.0);
	GtkWidget*   slider = new_hscale(min, max, step);
	gtk_range_set_value(GTK_RANGE(slider), deft);
	if (points) {
		g_signal_connect(G_OBJECT(slider),
		                 "format-value", G_CALLBACK(scale_format), points);
	}

	g_signal_connect(G_OBJECT(slider),
	                 "value-changed", G_CALLBACK(slider_changed), port);

	return slider;
}

static GtkWidget*
make_toggle(struct Port* port, float deft)
{
	GtkWidget* check = gtk_check_button_new();
	if (deft) {
		gtk_toggle_button_set_active(GTK_TOGGLE_BUTTON(check), TRUE);
	}
	g_signal_connect(G_OBJECT(check),
	                 "toggled", G_CALLBACK(toggle_changed), port);
	return check;
}

static GtkWidget*
build_control_widget(Jalv* jalv, GtkWidget* window)
{
	LilvNode*  lv2_sampleRate = lilv_new_uri(jalv->world, LV2_CORE__sampleRate);
	LilvNode*  lv2_integer    = lilv_new_uri(jalv->world, LV2_CORE__integer);
	LilvNode*  lv2_toggled    = lilv_new_uri(jalv->world, LV2_CORE__toggled);
	LilvNode*  lv2_enum       = lilv_new_uri(jalv->world, LV2_CORE__enumeration);
	LilvNode*  lv2_log        = lilv_new_uri(jalv->world, LV2_PORT_PROPS__logarithmic);
	LilvNode*  rdfs_comment   = lilv_new_uri(jalv->world, LILV_NS_RDFS "comment");
	GtkWidget* port_table     = gtk_table_new(jalv->num_ports, 2, false);
	float*     defaults       = calloc(jalv->num_ports, sizeof(float));
	float*     mins           = calloc(jalv->num_ports, sizeof(float));
	float*     maxs           = calloc(jalv->num_ports, sizeof(float));
	int        num_controls   = 0;
	lilv_plugin_get_port_ranges_float(jalv->plugin, mins, maxs, defaults);
	for (unsigned i = 0; i < jalv->num_ports; i++) {
		if (jalv->ports[i].type != TYPE_CONTROL) {
			continue;
		}
		++num_controls;

		const LilvPort* port = jalv->ports[i].lilv_port;
		LilvNode*       name = lilv_port_get_name(jalv->plugin, port);

		if (lilv_port_has_property(jalv->plugin, port, lv2_sampleRate)) {
			mins[i] *= jalv->sample_rate;
			maxs[i] *= jalv->sample_rate;
		}

		/* Get scale points */
		LilvScalePoints* sp     = lilv_port_get_scale_points(jalv->plugin, port);
		GHashTable*      points = NULL;
		if (sp) {
			points = g_hash_table_new(g_double_hash, g_double_equal);
			gdouble* values = malloc(lilv_scale_points_size(sp) * sizeof(gdouble));
			int      idx    = 0;
			LILV_FOREACH(scale_points, s, sp) {
				const LilvScalePoint* p = lilv_scale_points_get(sp, s);
				values[idx] = lilv_node_as_float(lilv_scale_point_get_value(p));
				char* label = g_strdup(
					lilv_node_as_string(lilv_scale_point_get_label(p)));
				g_hash_table_insert(points, values + idx, label);
				++idx;
			}
			lilv_scale_points_free(sp);
		}

		/* Make control */
		GtkWidget* control    = NULL;
		bool       is_integer = lilv_port_has_property(
			jalv->plugin, port, lv2_integer);
		if (lilv_port_has_property(jalv->plugin, port, lv2_toggled)) {
			control = make_toggle(&jalv->ports[i], defaults[i]);
		} else if (lilv_port_has_property(jalv->plugin, port, lv2_enum)
		           || (is_integer && points &&
		               (g_hash_table_size(points)
		                == (unsigned)(maxs[i] - mins[i] + 1)))) {
			control = make_combo(&jalv->ports[i], points, defaults[i]);
		} else if (lilv_port_has_property(jalv->plugin, port, lv2_log)) {
			control = make_log_slider(&jalv->ports[i], points,
			                          mins[i], maxs[i], defaults[i]);
		} else {
			control = make_slider(&jalv->ports[i], points, is_integer,
			                      mins[i], maxs[i], defaults[i]);
		}
		jalv->ports[i].widget = control;

		/* Set tooltip text */
		LilvNodes* comments = lilv_port_get_value(
			jalv->plugin, port, rdfs_comment);
		if (comments) {
			gtk_widget_set_tooltip_text(
				control, lilv_node_as_string(lilv_nodes_get_first(comments)));
		}
		lilv_nodes_free(comments);

		/* Add control table row */
		GtkWidget* label  = gtk_label_new(NULL);
		gchar*     markup = g_markup_printf_escaped(
			"<span font_weight=\"bold\">%s:</span>",
			lilv_node_as_string(name));
		gtk_label_set_markup(GTK_LABEL(label), markup);
		g_free(markup);
		gtk_misc_set_alignment(GTK_MISC(label), 1.0, 0.5);
		gtk_table_attach(GTK_TABLE(port_table),
		                 label,
		                 0, 1, i, i + 1,
		                 GTK_FILL, GTK_FILL | GTK_EXPAND, 15, 15);
		gtk_table_attach(GTK_TABLE(port_table), control,
		                 1, 2, i, i + 1,
		                 GTK_FILL | GTK_EXPAND, 0, 0, 0);
		lilv_node_free(name);
	}

	free(defaults);
	free(mins);
	free(maxs);
	lilv_node_free(lv2_sampleRate);
	lilv_node_free(lv2_integer);
	lilv_node_free(lv2_toggled);
	lilv_node_free(lv2_enum);
	lilv_node_free(rdfs_comment);

	if (num_controls > 0) {
		gtk_window_set_resizable(GTK_WINDOW(window), TRUE);
		GtkWidget* alignment = gtk_alignment_new(0.5, 0.0, 1.0, 0.0);
		gtk_alignment_set_padding(GTK_ALIGNMENT(alignment), 0, 0, 8, 8);
		gtk_container_add(GTK_CONTAINER(alignment), port_table);
		return alignment;
	} else {
		gtk_widget_destroy(port_table);
		GtkWidget* button = gtk_button_new_with_label("Close");
		g_signal_connect_swapped(
			button, "clicked", G_CALLBACK(gtk_widget_destroy), window);
		gtk_window_set_resizable(GTK_WINDOW(window), FALSE);
		return button;
	}
}

int
jalv_open_ui(Jalv* jalv)
{
	GtkWidget* window = gtk_window_new(GTK_WINDOW_TOPLEVEL);
	jalv->window = window;
	jalv->has_ui = TRUE;

	g_signal_connect(window, "destroy",
	                 G_CALLBACK(on_window_destroy), jalv);

	LilvNode* name = lilv_plugin_get_name(jalv->plugin);
	gtk_window_set_title(GTK_WINDOW(window), lilv_node_as_string(name));
	lilv_node_free(name);

	GtkWidget* vbox      = new_box(false, 0);
	GtkWidget* menu_bar  = gtk_menu_bar_new();
	GtkWidget* file      = gtk_menu_item_new_with_mnemonic("_File");
	GtkWidget* file_menu = gtk_menu_new();

	GtkAccelGroup* ag = gtk_accel_group_new();
	gtk_window_add_accel_group(GTK_WINDOW(window), ag);

	GtkWidget* save = gtk_image_menu_item_new_from_stock(GTK_STOCK_SAVE, ag);
	GtkWidget* quit = gtk_image_menu_item_new_from_stock(GTK_STOCK_QUIT, ag);

	gtk_menu_item_set_submenu(GTK_MENU_ITEM(file), file_menu);
	gtk_menu_shell_append(GTK_MENU_SHELL(file_menu), save);
	gtk_menu_shell_append(GTK_MENU_SHELL(file_menu), quit);
	gtk_menu_shell_append(GTK_MENU_SHELL(menu_bar), file);

	GtkWidget* presets      = gtk_menu_item_new_with_mnemonic("_Presets");
	GtkWidget* presets_menu = gtk_menu_new();
	GtkWidget* save_preset  = gtk_menu_item_new_with_mnemonic(
		"_Save Preset...");
	gtk_menu_item_set_submenu(GTK_MENU_ITEM(presets), presets_menu);
	gtk_menu_shell_append(GTK_MENU_SHELL(presets_menu), save_preset);
	gtk_menu_shell_append(GTK_MENU_SHELL(presets_menu),
	                      gtk_separator_menu_item_new());
	gtk_menu_shell_append(GTK_MENU_SHELL(menu_bar), presets);

	jalv_load_presets(jalv, add_preset_to_menu, presets_menu);

	gtk_container_add(GTK_CONTAINER(window), vbox);
	gtk_box_pack_start(GTK_BOX(vbox), menu_bar, FALSE, FALSE, 0);

	g_signal_connect(G_OBJECT(quit), "activate",
	                 G_CALLBACK(on_quit_activate), window);

	g_signal_connect(G_OBJECT(save), "activate",
	                 G_CALLBACK(on_save_activate), jalv);

	g_signal_connect(G_OBJECT(save_preset), "activate",
	                 G_CALLBACK(on_save_preset_activate), jalv);

	/* Create/show alignment to contain UI (whether custom or generic) */
	GtkWidget* alignment = gtk_alignment_new(0.5, 0.5, 1.0, 1.0);
	gtk_box_pack_start(GTK_BOX(vbox), alignment, TRUE, TRUE, 0);
	gtk_widget_show(alignment);

	/* Attempt to instantiate custom UI if necessary */
	if (jalv->ui && !jalv->opts.generic_ui) {
		jalv_ui_instantiate(jalv, jalv_native_ui_type(jalv), alignment);
	}

	if (jalv->ui_instance) {
		GtkWidget* widget = (GtkWidget*)suil_instance_get_widget(
			jalv->ui_instance);

		gtk_container_add(GTK_CONTAINER(alignment), widget);
		gtk_window_set_resizable(GTK_WINDOW(window), jalv_ui_is_resizable(jalv));
		gtk_widget_show_all(vbox);
	} else {
		GtkWidget* controls   = build_control_widget(jalv, window);
		GtkWidget* scroll_win = gtk_scrolled_window_new(NULL, NULL);
		gtk_scrolled_window_add_with_viewport(
			GTK_SCROLLED_WINDOW(scroll_win), controls);
		gtk_scrolled_window_set_policy(
			GTK_SCROLLED_WINDOW(scroll_win),
			GTK_POLICY_AUTOMATIC, GTK_POLICY_AUTOMATIC);
		gtk_container_add(GTK_CONTAINER(alignment), scroll_win);
		gtk_widget_show_all(vbox);

		GtkRequisition controls_size, box_size;
		size_request(GTK_WIDGET(controls), &controls_size);
		size_request(GTK_WIDGET(vbox), &box_size);

		gtk_window_set_default_size(
			GTK_WINDOW(window),
			MAX(MAX(box_size.width, controls_size.width) + 24, 640),
			box_size.height + controls_size.height);
	}

	g_timeout_add(1000 / jalv->ui_update_hz,
	              (GSourceFunc)jalv_emit_ui_events, jalv);

	gtk_window_present(GTK_WINDOW(window));

	gtk_main();
	zix_sem_post(jalv->done);
	return 0;
}