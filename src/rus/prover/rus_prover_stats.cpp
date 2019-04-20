#include <cmath>
#include <numeric>
#include "rus_prover_node.hpp"

namespace mdl { namespace rus { namespace prover {

struct CTimeStats {
	// map arg stands for the matrix number
	cmap<uint, uint> sequential;
	cmap<uint, uint> matrix;
};

// map arg stands for unification cardinality
static cmap<uint, CTimeStats> cstats;

void add_sequential_stats(uint card, uint count, uint time) {
	cmap<uint, CTimeStats>::accessor a;
	cstats.insert(a, card);
	cmap<uint, uint>::accessor b;
	a->second.sequential.insert(b, count);
	b->second = time;
}

void add_matrix_stats(uint card, uint count, uint time) {
	cmap<uint, CTimeStats>::accessor a;
	cstats.insert(a, card);
	cmap<uint, uint>::accessor b;
	a->second.matrix.insert(b, count);
	b->second = time;
}

struct TimeStats {
	// map arg stands for the matrix number
	map<uint, uint> sequential;
	map<uint, uint> matrix;
};

// map arg stands for unification cardinality
map<uint, TimeStats> make_stats(const cmap<uint, CTimeStats>& s) {
	map<uint, TimeStats> ret;
	for (const auto& p : s) {
		uint card = p.first;
		for (const auto& q : p.second.sequential) {
			uint count = q.first;
			uint time =  q.second;
			ret[card].sequential[count] = time;
		}
		for (const auto& q : p.second.matrix) {
			uint count = q.first;
			uint time =  q.second;
			ret[card].matrix[count] = time;
		}
	}
	return ret;
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

void print_down_unification_statistics() {
	constexpr uint N = 10;
	uint max_size = 0;
	uint sample_size = 0;

	map<uint, TimeStats> stats = make_stats(cstats);

	for (const auto& p : stats) {
		if (p.first > max_size) max_size = p.first;
		if (p.second.sequential.size() != p.second.matrix.size()) {
			throw Error("sample sizes must be equal");
		}
		sample_size += p.second.sequential.size();
	}
	uint m = (1 << (N + 1)) - 1;
	double factor = static_cast<double>(max_size) / m;
	cout << "max size: " << max_size << endl;
	cout << "sample size: " << sample_size << endl;
	cout << "Sz_from\tsz_to\tsize\tseq\tmatrix\tratio\tavg_rat\tdev_rat\tmin_rat\tmax_rat\ttotal_seq\ttotal_mat" << endl;
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
		if (seq_slices_size != mat_slices_size) {
			throw Error("slices sizes must be equal");
		}
		cout << lower_boundary << "\t" << upper_boundary << "\t" << seq_slices_size << "\t";

		avg_times_stats(cout, seq_slices, mat_slices);
		relative_times_stats(cout, seq_slices, mat_slices);
		total_times_stats(cout, seq_slices, mat_slices);

		lower_boundary = upper_boundary;
		cout << endl;
	}
	cout << endl;
}

}}}

