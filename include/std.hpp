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
//#include <variant>
#include <algorithm>
#include <exception>
#include <stdexcept>
#include <ostream>
#include <iostream>
#include <iomanip>
#include <string>
#include <vector>
#include <array>
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
#include <memory>
#include <unordered_map>
#include <unordered_set>

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

#include <boost/filesystem.hpp>
#include <boost/algorithm/string.hpp>
#include <boost/any.hpp>
#include <boost/variant.hpp>
#include <boost/program_options.hpp>

#include "config.h"

// TBB headers
#include "tbb/concurrent_vector.h"
#include "tbb/concurrent_hash_map.h"
#include "tbb/concurrent_queue.h"
#include "tbb/blocked_range.h"
#include "tbb/parallel_for.h"

#define iterate(N, B) for (int i = 0; i < (N); ++ i) { (B); }

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
	using std::stringstream;
	using std::ostringstream;
	using std::string;
	using std::cout;
	using std::cerr;
	using std::endl;
	using std::flush;
	using std::to_string;
	
	typedef std::uint32_t uint;

	//using std::variant;
	using std::vector;
	using std::array;
	using std::set;
	using std::deque;
	using std::queue;
	using std::stack;
	using std::map;
	using std::pair;
	using std::bitset;
	using std::thread;
	using std::mutex;
	using std::unordered_map;
	using std::unordered_set;

	using std::unique_ptr;
	using std::shared_ptr;
	using std::weak_ptr;
	using std::make_shared;
	using std::make_unique;

	using std::for_each;
	using std::function;

	using boost::any;

	namespace po = boost::program_options;

	template<typename K, typename T, typename H = tbb::tbb_hash_compare<K>, typename A = tbb::tbb_allocator<std::pair<K, T>>>
	using cmap = tbb::interface5::concurrent_hash_map<K, T, H, A>;
	template<typename T, typename A = tbb::cache_aligned_allocator<T>>
	using cvector = tbb::concurrent_vector<T, A>;
}

#define UNDEF_UINT 0xFFFFFFFF

