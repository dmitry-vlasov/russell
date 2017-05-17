#pragma once

#include "std.hpp"

namespace mdl {

class Timer;

ostream& operator << (ostream& os, const Timer& t);

class Timer {
public :
	Timer (const bool brief = false);

	void start();
	void stop();
	void mark();
	void clear();

	double getMicroseconds() const;
	double getMilliseconds() const;
	double getSeconds() const;
	double getMinutes() const;
	double getHours() const;
	double getCumulativeSeconds() const;
	double getCumulativeMinutes() const;
	double getCumulativeHours() const;

	bool isUsed() const;
	bool isOn() const;
	bool isOff() const;
	bool isNegligible() const;

	void setShowCumulativeTime (const bool = true) const;
	bool getShowCumulativeTime() const;

	void operator = (const Timer&);
	void operator += (const Timer&);
	void operator /= (const double);

	timeval getDelta() const;
	timeval getCumulative() const;

	void setDelta (timeval);
	void setCumulative (timeval);


	static void addTime (timeval&, const timeval);

	enum {
		MICROSECONDS_IN_SECOND      = 1000000,
		MICROSECONDS_IN_MILLISECOND = 1000,
		MILLISECONDS_IN_SECOND      = 1000
	};

	void showTime(string&, const timeval&) const;

	string show() const {
		ostringstream os;
		os << *this;
		return os.str();
	}

	bool isOn_;
	bool isUsed_;
	bool brief_;

	timeval startTime_;
	timeval midTime_;
	timeval stopTime_;

	timeval deltaTime_;
	timeval cumulativeTime_;

	mutable bool showCumulativeTime_;
};

inline string show(const Timer& tm) { return tm.show(); }

}


