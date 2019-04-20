#include <cmath>
#include <rus_ast.hpp>

namespace mdl { namespace rus { namespace expr {

struct Stats {
	void add(const Expr* e) {
		uint len = e->tree()->len();
		lengths.push_back(len);
		avg_len = -1;
		if (max_len < len) {
			max_len = len;
			max_len_expr = e;
		}
		needs_computation = true;
	}
	uint maxLen() { compute_expr_stats(); return max_len; }
	uint avgLen() { compute_expr_stats(); return avg_len; }
	uint devLen() { compute_expr_stats(); return dev_len; }
	const Expr* maxLenExpr() { return max_len_expr; }
	static Stats& stats() { static Stats stats_; return stats_; }

private:
	void compute_expr_stats() {
		if (needs_computation) {
			avg_len = avg(lengths);
			dev_len = stdev(lengths);
		}
	}
	bool needs_computation = true;
	uint max_len = 0;
	vector<uint> lengths;
	double avg_len = -1;
	double dev_len = -1;
	const Expr* max_len_expr = nullptr;
};

}}} // namespace mdl::rus::expr
