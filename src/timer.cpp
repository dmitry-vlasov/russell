/*****************************************************************************/
/* Project name:    nstd - non-standard library                              */
/* File name:       nstd_misc_Timer.cpp                                      */
/* Description:     simple timer                                             */
/* Copyright:       (c) 2006-2009 Dmitri Vlasov                              */
/* Author:          Dmitri Yurievich Vlasov, Novosibirsk, Russia             */
/* Email:           vlasov at academ.org                                     */
/* URL:             http://mathdevlanguage.sourceforge.net                   */
/* Modified by:                                                              */
/* License:         GNU General Public License Version 3                     */
/*****************************************************************************/

#include "timer.hpp"

namespace mdl {

	Timer :: Timer (const bool brief) :
	isOn_ (false),
	isUsed_ (false),
	brief_ (brief),
	startTime_ (),
	midTime_ (),
	stopTime_ (),
	deltaTime_ (),
	cumulativeTime_ (),
	showCumulativeTime_ (false) {
		clear();
	}
	void
	Timer :: start()
	{
		isUsed_ = true;
		isOn_ = true;
		:: gettimeofday (&startTime_, NULL);
	}
	void
	Timer :: stop()
	{
		if (!isOn_) {
			return;
		}
		:: gettimeofday (&stopTime_, NULL);

		deltaTime_.tv_sec = stopTime_.tv_sec - startTime_.tv_sec;
		deltaTime_.tv_usec = stopTime_.tv_usec - startTime_.tv_usec;
		if (deltaTime_.tv_usec < 0) {
			deltaTime_.tv_usec += MICROSECONDS_IN_SECOND;
			-- deltaTime_.tv_sec;
		} else if (deltaTime_.tv_usec >= MICROSECONDS_IN_SECOND) {
			deltaTime_.tv_usec -= MICROSECONDS_IN_SECOND;
			++ deltaTime_.tv_sec;
		}
		addTime (cumulativeTime_, deltaTime_);
		isOn_ = false;
	}
	void
	Timer :: mark()
	{
		if (!isOn_) {
			return;
		}
		:: gettimeofday (&midTime_, NULL);
		deltaTime_.tv_sec = midTime_.tv_sec - startTime_.tv_sec;
		deltaTime_.tv_usec = midTime_.tv_usec - startTime_.tv_usec;
		if (deltaTime_.tv_usec < 0) {
			deltaTime_.tv_usec += MICROSECONDS_IN_SECOND;
			-- deltaTime_.tv_sec;
		} else if (deltaTime_.tv_usec >= MICROSECONDS_IN_SECOND) {
			deltaTime_.tv_usec -= MICROSECONDS_IN_SECOND;
			++ deltaTime_.tv_sec;
		}
	}

	void
	Timer :: clear()
	{
		isOn_ = false;
		startTime_.tv_sec  = 0;
		startTime_.tv_usec = 0;
		midTime_.tv_sec    = 0;
		midTime_.tv_usec   = 0;
		stopTime_.tv_sec   = 0;
		stopTime_.tv_usec  = 0;
		cumulativeTime_.tv_sec  = 0;
		cumulativeTime_.tv_usec = 0;
	}
	double
	Timer :: getMicroseconds() const
	{
		if (!isUsed_) {
			return -1;
		}
		if (isOn_) {
			const_cast<Timer*>(this)->mark();
		}
		return
			static_cast<double>(deltaTime_.tv_usec) +
			static_cast<double>(deltaTime_.tv_sec) * MICROSECONDS_IN_SECOND;
	}
	double
	Timer :: getMilliseconds() const
	{
		if (!isUsed_) {
			return -1;
		}
		if (isOn_) {
			const_cast<Timer*>(this)->mark();
		}
		return
			static_cast<double>(deltaTime_.tv_usec) / MICROSECONDS_IN_MILLISECOND +
			static_cast<double>(deltaTime_.tv_sec) * MILLISECONDS_IN_SECOND;
	}
	double
	Timer :: getSeconds() const
	{
		if (!isUsed_) {
			return -1;
		}
		if (isOn_) {
			const_cast<Timer*>(this)->mark();
		}
		return
			static_cast<double>(deltaTime_.tv_usec) / MICROSECONDS_IN_SECOND +
			static_cast<double>(deltaTime_.tv_sec);
	}
	double
	Timer :: getMinutes() const
	{
		if (isUsed_) {
			return -1;
		}
		return getSeconds() / 60;
	}
	double
	Timer :: getHours() const
	{
		if (isUsed_) {
			return -1;
		}
		return getMinutes() / 60;
	}

	double
	Timer :: getCumulativeSeconds() const
	{
		if (isUsed_) {
			return -1;
		}
		return
			static_cast<double>(cumulativeTime_.tv_sec) +
			static_cast<double>(cumulativeTime_.tv_usec) / MICROSECONDS_IN_SECOND;
	}
	double
	Timer :: getCumulativeMinutes() const
	{
		if (isUsed_) {
			return -1;
		}
		return getCumulativeSeconds() / 60;
	}
	double
	Timer :: getCumulativeHours() const
	{
		if (isUsed_) {
			return -1;
		}
		return getCumulativeMinutes() / 60;
	}

	bool
	Timer :: isUsed() const {
		return isUsed_;
	}
	bool
	Timer :: isOn() const {
		return isOn_;
	}
	bool
	Timer :: isOff() const {
		return !isOn_;
	}

	void
	Timer :: setShowCumulativeTime (const bool value) const {
		showCumulativeTime_ = value;
	}
	bool
	Timer :: getShowCumulativeTime() const {
		return showCumulativeTime_;
	}

	void
	Timer :: operator = (const Timer& timer)
	{
		isOn_   = timer.isOn_;
		isUsed_ = timer.isUsed_;
		brief_  = timer.brief_;

		startTime_ = timer.startTime_;
		midTime_   = timer.midTime_;
		stopTime_  = timer.stopTime_;
		deltaTime_ = timer.deltaTime_;

		cumulativeTime_     = timer.cumulativeTime_;
		showCumulativeTime_ = timer.showCumulativeTime_;
	}
	void
	Timer :: operator += (const Timer& timer)
	{
		isUsed_ = true;
		addTime (deltaTime_,      timer.deltaTime_);
		addTime (cumulativeTime_, timer.deltaTime_);
	}
	void
	Timer :: operator /= (const double factor)
	{
		double seconds =
			deltaTime_.tv_sec +
			static_cast<double>(deltaTime_.tv_usec) / MICROSECONDS_IN_SECOND;
		double scaled = seconds / factor;
		deltaTime_.tv_sec = scaled;
		deltaTime_.tv_usec = (scaled - deltaTime_.tv_sec) * MICROSECONDS_IN_SECOND;
	}

	timeval
	Timer :: getDelta() const {
		return deltaTime_;
	}
	timeval
	Timer :: getCumulative() const {
		return cumulativeTime_;
	}

	void
	Timer :: setDelta (timeval delta)
	{
		isUsed_ = true;
		deltaTime_ = delta;
	}
	void
	Timer :: setCumulative (timeval cumulative)
	{
		isUsed_ = true;
		cumulativeTime_ = cumulative;
	}

	void
	Timer :: show(string& str) const
	{
		if (!isUsed_) {
			str += "unknown period";
			return;
		}
		if (showCumulativeTime_) {
			showTime(str, cumulativeTime_);
		} else {
			showTime(str, deltaTime_);
		}
	}

	/****************************
	 *		Private members
	 ****************************/
	void
	Timer :: showTime(string& str, const timeval& time) const
	{
		std :: ostringstream oss;
		if (time.tv_sec == 0) {
			if (time.tv_usec < 1000) {
				oss << time.tv_usec;
				if (brief_) {
					oss << " us";
				} else {
					oss << " microseconds";
					oss << " (" << getSeconds() << " s)";
				}
			} else {
				oss << static_cast<double>(time.tv_usec) / 1000;
				if (brief_) {
					oss << " ms";
				} else {
					oss << " milliseconds";
					oss << " (" << getSeconds() << " s)";
				}
			}
		} else if (time.tv_sec < 60) {
			oss << getSeconds();
			if (brief_) {
				oss << " s";
			} else {
				oss << " seconds";
			}
		} else {
			const std :: tm*
				t = std :: gmtime (&time.tv_sec);
			enum {
				BUFFER_SIZE = 256
			};
			char s [BUFFER_SIZE];
			if (time.tv_sec < 60 * 60) {
				if (brief_) {
					std :: strftime (s, BUFFER_SIZE, "%M m, %S s", t);
					oss << s;
				} else {
					std :: strftime (s, BUFFER_SIZE, "%M minutes, %S seconds", t);
					oss << s << " (" <<  getSeconds() << " s)";
				}
			} else {
				if (brief_) {
					std :: strftime (s, BUFFER_SIZE, "%H h, %M m, %S s", t);
					oss << s;
				} else {
					std :: strftime (s, BUFFER_SIZE, "%H hours, %M minutes, %S seconds", t);
					oss << s << " (" <<  getSeconds() << " s)";
				}
			}
		}
		str += oss.str();
	}
	void
	Timer :: addTime (timeval& time_1, const timeval time_2)
	{
		time_1.tv_sec += time_2.tv_sec;
		time_1.tv_usec += time_2.tv_usec;
		if (time_1.tv_usec >= MICROSECONDS_IN_SECOND) {
			time_1.tv_usec -= MICROSECONDS_IN_SECOND;
			++ time_1.tv_sec;
		}
	}
} // mdl


