#pragma once

#include "std.hpp"

namespace mdl {

struct Timer {
	Timer(const Timer&) = default;
	Timer() {
		start();
	}

	void start() {
		clear();
		::gettimeofday(&startTime_, nullptr);
	}

	void stop() {
		timeval stopTime;
		::gettimeofday(&stopTime, nullptr);
		deltaTime_.tv_sec = stopTime.tv_sec - startTime_.tv_sec;
		deltaTime_.tv_usec = stopTime.tv_usec - startTime_.tv_usec;
		if (deltaTime_.tv_usec < 0) {
			deltaTime_.tv_usec += MICROSECONDS_IN_SECOND;
			-- deltaTime_.tv_sec;
		} else if (deltaTime_.tv_usec >= MICROSECONDS_IN_SECOND) {
			deltaTime_.tv_usec -= MICROSECONDS_IN_SECOND;
			++ deltaTime_.tv_sec;
		}
	}

	double getMicroseconds() const {
		return
			static_cast<double>(deltaTime_.tv_usec) +
			static_cast<double>(deltaTime_.tv_sec) * MICROSECONDS_IN_SECOND;
	}

	double getMilliseconds() const {
		return
			static_cast<double>(deltaTime_.tv_usec) / MICROSECONDS_IN_MILLISECOND +
			static_cast<double>(deltaTime_.tv_sec) * MILLISECONDS_IN_SECOND;
	}

	double getSeconds() const {
		return
			static_cast<double>(deltaTime_.tv_usec) / MICROSECONDS_IN_SECOND +
			static_cast<double>(deltaTime_.tv_sec);
	}

	double getMinutes() const {
		return getSeconds() / 60;
	}

	double getHours() const {
		return getMinutes() / 60;
	}

	bool isNegligible() const {
		return getMilliseconds() < 1;
	}

	void operator += (const Timer& timer) {
		deltaTime_.tv_sec += timer.deltaTime_.tv_sec;
		deltaTime_.tv_usec += timer.deltaTime_.tv_usec;
		deltaTime_.tv_sec += deltaTime_.tv_usec / MICROSECONDS_IN_SECOND;
		deltaTime_.tv_usec = deltaTime_.tv_usec % MICROSECONDS_IN_SECOND;
	}

	void operator /= (const double factor) {
		double seconds =
			deltaTime_.tv_sec +
			static_cast<double>(deltaTime_.tv_usec) / MICROSECONDS_IN_SECOND;
		double scaled = seconds / factor;
		deltaTime_.tv_sec = scaled;
		deltaTime_.tv_usec = (scaled - deltaTime_.tv_sec) * MICROSECONDS_IN_SECOND;
	}

	Timer& operator = (const Timer&) = default;

	string show() const {
		std::ostringstream oss;
		if (deltaTime_.tv_sec == 0) {
			if (deltaTime_.tv_usec < 1000) {
				oss << deltaTime_.tv_usec << " us";
			} else {
				oss << static_cast<double>(deltaTime_.tv_usec) / 1000 << " ms";
			}
		} else if (deltaTime_.tv_sec < 60) {
			oss << getSeconds() << " s";
		} else {
			const std::tm* t = std::gmtime(&deltaTime_.tv_sec);
			enum { BUFFER_SIZE = 256 };
			char s [BUFFER_SIZE];
			if (deltaTime_.tv_sec < 60 * 60) {
				std::strftime(s, BUFFER_SIZE, "%M m, %S s", t);
				oss << s;
			} else {
				std::strftime(s, BUFFER_SIZE, "%H h, %M m, %S s", t);
				oss << s;
			}
		}
		return oss.str();
	}

private:
	enum {
		MICROSECONDS_IN_SECOND      = 1000'000,
		MICROSECONDS_IN_MILLISECOND = 1000,
		MILLISECONDS_IN_SECOND      = 1000
	};
	void clear() {
		startTime_.tv_sec  = 0;
		startTime_.tv_usec = 0;
		deltaTime_.tv_sec  = 0;
		deltaTime_.tv_usec = 0;
	}
	timeval startTime_;
	timeval deltaTime_;
};

inline ostream& operator << (ostream& os, const Timer& t) {
	os << t.show(); return os;
}

class Timeout : public std::exception {
public :
	Timeout (const string& str) throw() : msg("timeout: " + str) { }
	virtual ~Timeout() { }
	virtual const char* what() const throw() {
		return msg.c_str();
	}
	string msg;
};

struct Watchdog {
	Watchdog(uint m, const string& msg, bool s = true) : millis(m), message(msg), strict(s) { }

	bool isOverLimit() {
		timer.stop();
		return timer.getMilliseconds() > millis;
	}

	bool check() {
		bool ret = isOverLimit();
		if (strict && ret) {
			throw Timeout(message);
		}
		return ret;
	}

private:
	Timer timer;
	uint millis;
	string message;
	const bool strict;
};

}


