/*****************************************************************************/
/* Project name:    smm - verifier for the Simplified MetaMath language      */
/* File Name:       smm.hpp                                                  */
/* Description:     all smm modules                                          */
/* Copyright:       (c) 2006-2009 Dmitri Vlasov                              */
/* Author:          Dmitri Yurievich Vlasov, Novosibirsk, Russia             */
/* Email:           vlasov at academ.org                                     */
/* URL:             http://mathdevlanguage.sourceforge.net                   */
/* Modified by:                                                              */
/* License:         GNU General Public License Version 3                     */
/*****************************************************************************/

#pragma once

#include <memory>
#include <algorithm>
#include <exception>
#include <ostream>
#include <iostream>
#include <iomanip>
#include <string>
#include <vector>
#include <map>
#include <set>
#include <stack>
#include <deque>
#include <limits>
#include <iterator>
#include <bitset>
#include <utility>
#include <queue>
#include <thread>
#include <mutex>

#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <cctype>
#include <ctime>
#include <sstream>
#include <fstream>
#include <typeinfo>
#include <assert.h>

#include <pthread.h>

#include <time.h>
#include <stddef.h>
#include <stdint.h>
#include <math.h>
#include <unistd.h>
#include <malloc.h>
#include <system_error>
#include <sys/time.h>
#include <sys/stat.h>
#include <sys/types.h>

size_t get_total_mem();
size_t get_peak_RSS();
size_t get_current_RSS();
size_t get_current_free();

namespace mdl { 
	using std::size_t;
	using std::ptrdiff_t;
	using std::ostream;
	using std::ifstream;
	using std::ofstream;
	using std::ostringstream;
	using std::string;
	using std::cout;
	using std::cerr;
	using std::endl;
	using std::flush;
	using std::to_string;
	
	typedef std::uint32_t uint;

	using std::vector;
	using std::set;
	using std::deque;
	using std::queue;
	using std::stack;
	using std::map;
	using std::pair;
	using std::bitset;
	using std::thread;
	using std::mutex;
}


