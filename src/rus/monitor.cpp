#include <qt5/QtCore/QFileSystemWatcher>

#include "rus/globals.hpp"

namespace mdl {
namespace rus {


struct Monitor {
	QFileSystemWatcher watcher;
	Monitor() : watcher() { }
};

void monitor() {
	Monitor monitor;

}


}} // namespace mdl::rus

