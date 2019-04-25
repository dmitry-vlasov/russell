#include <cmath>
#include <numeric>
#include "rus_prover_node.hpp"

namespace mdl { namespace rus { namespace prover {

struct TimeStats {
	// map arg stands for the matrix number
	map<uint, uint> sequential;
	map<uint, uint> matrix;
};

struct Stats {
	map<uint, TimeStats> timeStats;
	map<string, Timer> timers;
};

// map arg stands for unification cardinality
static map<uint, TimeStats> stats;
static mutex m;

//static cmap<uint, Stats> cstats;

void add_sequential_stats(uint card, uint count, uint time) {
	//cmap<uint, Stats>::accessor a;
	//cstats.insert(a, std::this_thread::id())
	m.lock();
	stats[card].sequential[count] = time;
	m.unlock();
}

void add_matrix_stats(uint card, uint count, uint time) {
	m.lock();
	stats[card].matrix[count] = time;
	m.unlock();
}

typedef map<uint, const map<uint, uint>*> Slices;

uint slices_size(const Slices& slices) {
	uint sum_size = 0;
	for (auto slice : slices) {
		sum_size += slice.second->size();
	}
	return sum_size;
}

uint slices_total_time(const Slices& slices) {
	uint total_time = 0;
	for (auto slice : slices) {
		for (auto p : *slice.second) {
			total_time += p.second;
		}
	}
	return total_time;
}

uint slices_min_time(const Slices& slices) {
	uint min_time = INT_MAX;
	for (auto slice : slices) {
		for (auto p : *slice.second) {
			min_time = std::min(p.second, min_time);
		}
	}
	return min_time;
}

uint slices_max_time(const Slices& slices) {
	uint max_time = 0;
	for (auto slice : slices) {
		for (auto p : *slice.second) {
			max_time = std::max(p.second, max_time);
		}
	}
	return max_time;
}

double avg_slices(const Slices& slices) {
	double sum_val = 0;
	uint sum_size = 0;
	for (auto slice : slices) {
		for (auto p : *slice.second) {
			sum_val += p.second;
		}
		sum_size += slice.second->size();
	}
	return sum_size ? sum_val / sum_size : -1.0;
}

void avg_times_stats(std::ostream& os, const Slices& seq, const Slices& mat) {
	double avg_seq = avg_slices(seq);
	double avg_mat = avg_slices(mat);

	os << avg_seq << "\t" << avg_mat << "\t";
	os << avg_seq / avg_mat << "\t";
}

void relative_times_stats(std::ostream& os, const Slices& seq, const Slices& mat) {
	vector<double> ratios;
	for (auto slice : seq) {
		uint size = slice.first;
		for (const auto& q : *slice.second) {
			uint count = q.first;
			uint seq_time = q.second;
			uint mat_time = mat.at(size)->at(count);
			if (mat_time > 0) {
				double ratio = static_cast<double>(seq_time) / mat_time;
				ratios.push_back(ratio);
			}
		}
	}
	double avg_ratio = avg(ratios);
	double dev_ratio = stdev(ratios);
	double min_ratio = vect_min(ratios);
	double max_ratio = vect_max(ratios);

	os << avg_ratio << "\t" << dev_ratio << "\t";
	os << min_ratio << "\t" << max_ratio << "\t";
}

void total_times_stats(std::ostream& os, const Slices& seq, const Slices& mat) {
	uint seq_time = slices_total_time(seq);
	uint mat_time = slices_total_time(mat);
	os << seq_time << "\t" << mat_time << "\t";
}

void min_max_times_stats(std::ostream& os, const Slices& seq, const Slices& mat) {
	double min_seq = slices_min_time(seq);
	double max_seq = slices_max_time(seq);
	double min_mat = slices_min_time(mat);
	double max_mat = slices_max_time(mat);

	os << min_seq << "\t" << max_seq << "\t";
	os << min_mat << "\t" << max_mat << "\t";
}

void print_down_unification_statistics() {
	constexpr uint N = 10;
	uint max_size = 0;
	uint sample_size = 0;
	for (const auto& p : stats) {
		if (p.first > max_size) max_size = p.first;
		if (p.second.sequential.size() != p.second.matrix.size()) {
			cerr << "sample sizes must be equal: " << p.second.sequential.size() << " != " << p.second.matrix.size() << endl;
			//throw Error("sample sizes must be equal");
		}
		sample_size += p.second.sequential.size();
	}
	uint m = (1 << (N + 1)) - 1;
	double factor = static_cast<double>(max_size) / m;
	cout << "max size: " << max_size << endl;
	cout << "sample size: " << sample_size << endl;
	cout << "Sz_from\tsz_to\tsize\tseq\tmatrix\tratio\tavg_rat\tdev_rat\tmin_rat\tmax_rat\ttotal_seq\ttotal_mat\t";
	cout << "min_seq\tmax_seq\tmin_mat\tmax_mat\t" << endl;
	cout << "-------------------------------------------" << endl;
	uint lower_boundary = 0;
	uint i = 0;
	while (lower_boundary < max_size) {
		uint upper_boundary = std::min((1 << i++) * factor, static_cast<double>(max_size));
		if (lower_boundary == upper_boundary) {
			continue;
		}
		Slices seq_slices;
		Slices mat_slices;
		for (uint s = lower_boundary; s < upper_boundary; ++ s) {
			seq_slices[s] = &stats[s].sequential;
			mat_slices[s] = &stats[s].matrix;
		}
		uint seq_slices_size = slices_size(seq_slices);
		uint mat_slices_size = slices_size(mat_slices);
		if (seq_slices_size) {
			if (seq_slices_size != mat_slices_size) {
				cerr << "slices sizes must be equal: " << seq_slices_size << " != " << mat_slices_size << endl;
				//throw Error("slices sizes must be equal");
			}
			cout << lower_boundary << "\t" << upper_boundary << "\t" << seq_slices_size << "\t";

			avg_times_stats(cout, seq_slices, mat_slices);
			relative_times_stats(cout, seq_slices, mat_slices);
			total_times_stats(cout, seq_slices, mat_slices);
			min_max_times_stats(cout, seq_slices, mat_slices);
			cout << endl;
		}
		lower_boundary = upper_boundary;
	}
	cout << endl;
}

}}}

