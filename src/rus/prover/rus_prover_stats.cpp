#include <cmath>
#include <numeric>
#include "rus_prover_node.hpp"

namespace mdl { namespace rus { namespace prover {

map<uint, TimeStats> stats;

double avg(const vector<uint>& v) {
	return std::accumulate(v.begin(), v.end(), 0.0, [](uint a, uint s) { return a + s; }) / v.size();
}

double avg(const vector<const vector<uint>*>& vects) {
	double sum_val = 0;
	uint sum_size = 0;
	for (auto vect : vects) {
		for (uint v : *vect) {
			sum_val += v;
		}
		sum_size += vect->size();
	}
	return sum_size ? sum_val / sum_size : -1.0;
}

constexpr uint N = 10;

void print_down_unification_statistics() {

	uint max_size = 0;
	for (const auto& p : stats) {
		if (p.first > max_size) max_size = p.first;
	}
	uint m = (1 << (N + 1)) - 1;
	double factor = static_cast<double>(max_size) / m;
	cout << "max size: " << max_size << endl;
	//cout << "m: " << m << endl;
	//cout << "factor: " << factor << endl;

	cout << "Sz_from\tsz_to\tseq\tmatrix\tratio\tseq_size\tmat_size" << endl;
	cout << "-------------------------------------------" << endl;
	uint lower_boundary = 0;
	uint i = 0;
	while (lower_boundary < max_size) {
		uint upper_boundary = std::min((1 << i++) * factor, static_cast<double>(max_size));
		if (lower_boundary == upper_boundary) {
			continue;
		}
		vector<const vector<uint>*> seq_slices;
		vector<const vector<uint>*> mat_slices;
		for (uint s = lower_boundary; s < upper_boundary; ++ s) {
			seq_slices.push_back(&stats[s].sequential);
			mat_slices.push_back(&stats[s].matrix);
		}
		double avg_seq = avg(seq_slices);
		double avg_mat = avg(mat_slices);
		cout << lower_boundary << "\t" << upper_boundary << "\t";
		cout << avg_seq << "\t" << avg_mat << "\t";
		cout << avg_seq / avg_mat << "\t";
		//cout << p.second.sequential.size() << "\t" << p.second.matrix.size() << endl;
		lower_boundary = upper_boundary;
		cout << endl;
	}



	/*for (const auto& p : stats) {
		double avg_seq = p.second.sequential.size() ? avg(p.second.sequential) : -1.0;
		double avg_mat = p.second.matrix.size() ? avg(p.second.matrix) : -1.0;
		cout << p.first << "\t" << avg_seq << "\t" << avg_mat << "\t";
		cout << avg_seq / avg_mat << "\t";
		cout << p.second.sequential.size() << "\t" << p.second.matrix.size() << endl;
	}*/
	cout << endl;
}

}}}

