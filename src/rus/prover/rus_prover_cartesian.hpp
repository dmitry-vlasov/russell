#include "rus_prover_space.hpp"
#include "rus_prover_unify.hpp"

namespace mdl { namespace rus { namespace prover {

struct CartesianIter {
	CartesianIter();

	void addDim(uint d);
	void addFixed(uint i);
	void makeNext();
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
	string show() const;
	string current() const ;
	bool current_is(const vector<uint> ind) const;
	uint cardinality() const;
	bool isLast() const;

private:
	uint         size_;
	vector<uint> dims_;
	vector<uint> ind_;

	bool         hasNext_;
	bool         isEmpty_;
};

}}}
