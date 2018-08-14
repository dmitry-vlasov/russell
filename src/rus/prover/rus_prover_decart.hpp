#include "rus_prover_space.hpp"
#include "rus_prover_unify.hpp"

namespace mdl { namespace rus { namespace prover {

struct DecartIter {
	DecartIter() : size_(0), fixed_(-1), hasNext_(false), isEmpty_(false) { }

	void addDim(uint d) {
		++size_;
		if (d == 0) {
			isEmpty_ = true;
		}
		if (d > 1) {
			hasNext_ = true;
		}
		dims_.push_back(d);
		ind_.push_back(0);
	}
	void addFixed(uint i) {
		fixed_ = size_;
		++size_;
		dims_.push_back(-1);
		ind_.push_back(i);
	}
	void makeNext() {
		for (uint i = 0; i < size_; ++ i) {
			if (dims_[i] == -1) {
				continue;
			}
			if (ind_[i] + 1 < dims_[i]) {
				++ ind_[i];
				hasNext_ = !isLast();
				return;
			} else {
				ind_[i] = 0;
			}
		}
		assert(false && "this execution point should be unreacheable");
	}
	bool hasNext() const {
		return size_ && hasNext_;
	}
	bool empty() const {
		return size_ && isEmpty_;
	}
	uint size() const {
		return size_;
	}
	uint operator[] (uint i) const {
		return ind_[i];
	}
	const vector<uint>& dims() const {
		return dims_;
	}
	string show() const {
		if (empty()) return "empty";
		string ret;
		ret += "size: " + to_string(size_) + ", ";
		ret += "dims: [";
		for (auto d : dims_) {
			ret += (d == -1 ? string("N") : to_string(d)) + " ";
		}
		ret += "]";
		return ret;
	}
	string current() const {
		if (empty()) return "empty";
		string ret = "[";
		for (auto i : ind_) {
			ret += to_string(i) + " ";
		}
		ret += "]";
		return ret;
	}
	bool current_is(const vector<uint> ind) const {
		if (ind.size() != ind_.size()) return false;
		for (uint i = 0; i < ind.size(); ++ i) {
			if (ind[i] != ind_[i]) {
				return false;
			}
		}
		return true;
	}
	uint cardinality() const {
		if (!size_ || empty()) {
			return 0;
		}
		uint card = 1;
		for (uint i = 0; i < size_; ++ i) {
			if (dims_[i] != -1) {
				card *= dims_[i];
			}
		}
		return card;
	}
	bool isLast() const {
		for (uint i = 0; i < size_; ++ i) {
			if (dims_[i] != -1 && (ind_[i] + 1 != dims_[i])) {
				return false;
			}
		}
		return true;
	}

private:
	uint         size_;
	uint         fixed_;
	vector<uint> dims_;
	vector<uint> ind_;

	bool         hasNext_;
	bool         isEmpty_;
};

}}}

