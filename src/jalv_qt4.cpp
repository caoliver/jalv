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

#include "jalv_internal.h"

#include <QApplication>
#include <QMainWindow>
#include <QMenuBar>
#include <QPushButton>
#include <QTimer>

static QApplication* app = NULL;

extern "C" {

int
jalv_init(int* argc, char*** argv, JalvOptions* opts)
{
	app = new QApplication(*argc, *argv, true);
	return 0;
}

const char*
jalv_native_ui_type(Jalv* jalv)
{
	return "http://lv2plug.in/ns/extensions/ui#Qt4UI";
}

int
jalv_ui_resize(Jalv* jalv, int width, int height)
{
	if (jalv->ui_instance && width > 0 && height > 0) {
		QWidget* widget = (QWidget*)suil_instance_get_widget(jalv->ui_instance);
		if (widget) {
			widget->resize(width, height);
		}
	}
	return 0;
}

void
jalv_ui_port_event(Jalv*       jalv,
                   uint32_t    port_index,
                   uint32_t    buffer_size,
                   uint32_t    protocol,
                   const void* buffer)
{
}

class Timer : public QTimer {
public:
	explicit Timer(Jalv* j) : jalv(j) {}

	void timerEvent(QTimerEvent* e) {
		jalv_emit_ui_events(jalv);
	}

private:
	Jalv* jalv;
};

int
jalv_open_ui(Jalv* jalv)
{
	QMainWindow* win         = new QMainWindow();
	QMenu*       file_menu   = win->menuBar()->addMenu("&File");
	QAction*     quit_action = new QAction("&Quit", win);

	QObject::connect(quit_action, SIGNAL(triggered()), win, SLOT(close()));
	quit_action->setShortcuts(QKeySequence::Quit);
	quit_action->setStatusTip("Quit Jalv");
	file_menu->addAction(quit_action);

	if (jalv->ui) {
		jalv_ui_instantiate(jalv, jalv_native_ui_type(jalv), win);
	}

	if (jalv->ui_instance) {
		QWidget* widget = (QWidget*)suil_instance_get_widget(jalv->ui_instance);
		win->setCentralWidget(widget);
	} else {
		QPushButton* button = new QPushButton("Close");
		win->setCentralWidget(button);
		QObject::connect(button, SIGNAL(clicked()), app, SLOT(quit()));
	}
	app->connect(app, SIGNAL(lastWindowClosed()), app, SLOT(quit()));
	win->show();

	Timer* timer = new Timer(jalv);
	timer->start(1000 / jalv->ui_update_hz);

	int ret = app->exec();
	zix_sem_post(jalv->done);
	return ret;
}

int
jalv_close_ui(Jalv* jalv)
{
	app->quit();
	return 0;
}

}  // extern "C"
