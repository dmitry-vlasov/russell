#pragma once

#define BOOST_LOG_DYN_LINK 1 // necessary when linking the boost_log library dynamically

#include <boost/log/trivial.hpp>
#include <boost/log/sources/global_logger_storage.hpp>

// the logs are also written to LOGFILE
#define LOGFILE "/var/tmp/mdl.log"

// just log messages with severity >= SEVERITY_THRESHOLD are written
#define SEVERITY_THRESHOLD logging::trivial::warning

// register a global logger
BOOST_LOG_GLOBAL_LOGGER(logger, boost::log::sources::severity_logger_mt<boost::log::trivial::severity_level>)

// just a helper macro used by the macros below - don't use it in your code
#define LOG(severity) BOOST_LOG_SEV(logger::get(),boost::log::trivial::severity)

// ===== log macros =====
#define LOG_TRACE   LOG(trace)
#define LOG_DEBUG   LOG(debug)
#define LOG_INFO    LOG(info)
#define LOG_WARNING LOG(warning)
#define LOG_ERROR   LOG(error)
#define LOG_FATAL   LOG(fatal)

/*
 Example of usage:

 int main() {
    LOG_TRACE << "this is a trace message";
    LOG_DEBUG << "this is a debug message";
    LOG_WARNING << "this is a warning message";
    LOG_ERROR << "this is an error message";
    LOG_FATAL << "this is a fatal error message";
    return 0;
}

Output in log file (SEVERITY_THRESHOLD = warning level):

0000003 | 2014-12-14, 19:54:53.775614 [warning] - this is a warning message
0000004 | 2014-12-14, 19:54:53.775747 [error] - this is an error message
0000005 | 2014-12-14, 19:54:53.775781 [fatal] - this is a fatal error message

 *
 */
