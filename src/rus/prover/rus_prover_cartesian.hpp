#include "rus_prover_space.hpp"
#include "rus_prover_unify.hpp"

namespace mdl { namespace rus { namespace prover {

struct CartesianIter {
	void addDim(uint d);
	void addFixed(uint i);
	void makeNext();
	bool hasNext() const;
	//bool empty() const { return cardinality() == 0; }
	uint size() const { return dims_.size(); }
	uint operator[] (uint i) const { return ind_[i]; }
	const vector<uint>& dims() const { return dims_; }

	string show() const;
	string current() const ;
	bool current_is(const vector<uint> ind) const;
	uint cardinality() const;

private:
	vector<uint> dims_;
	vector<uint> ind_;
};

template<class Data>
struct CartesianMap {
	void addDim(const vector<Data>& data) {
		dims_.push_back(data);
		iter_.addDim(data.size());
	}
	void addFixed(const vector<Data>& data, uint i) {
		dims_.push_back(data);
		iter_.addFixed(i);
	}

	bool hasNext() const { return iter_.hasNext(); }
	uint size() const { return iter_.size(); }
	Data operator[] (uint i) const {
		return dims_[i][iter_[i]];
	}
	vector<Data> data() const {
		vector<Data> ret;
		for (uint j = 0; j < iter_.size(); ++ j) {
			ret.push_back(dims_[j][iter_[j]]);
		};
		return ret;
	}

private:
	CartesianIter iter_;
	vector<vector<Data>>& dims_;
};

}}}
