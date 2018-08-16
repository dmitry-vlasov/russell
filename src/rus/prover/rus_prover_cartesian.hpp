#include "rus_prover_space.hpp"
#include "rus_prover_unify.hpp"

namespace mdl { namespace rus { namespace prover {

struct CartesianIter {
	CartesianIter() = default;
	CartesianIter(const vector<uint>&);

	void incDim();
	void incSize();

	void addDim(uint d);
	void addFixed(uint d, uint i);

	void fix(uint i) { fixed_[i] = true; }
	void unfix(uint i) { fixed_[i] = false; }

	void reset(bool drop_fixed = true);
	void makeNext();
	bool hasNext() const;
	uint size() const { return dims_.size(); }
	uint card() const;
	uint operator[] (uint i) const { return ind_[i]; }
	uint& operator[] (uint i) { return ind_[i]; }
	const vector<uint>& dims() const { return dims_; }

	string show() const;
	string current() const ;
	bool current_is(const vector<uint> ind) const;

private:
	vector<uint> dims_;
	vector<bool> fixed_;
	vector<uint> ind_;
};

template<class Data>
struct CartesianProduct {
	CartesianProduct() = default;
	CartesianProduct(const vector<vector<Data>>& d) : data_(d) {
		for (const auto& v : data_) {
			addDim(v.size());
		}
	}

	void incDim(Data d) {
		data_[data_.size() - 1].push_back(d);
		iter_.incDim();
	}
	void incSize() {
		data_.push_back(vector<Data>());
		iter_.incSize();
	}

	void addDim(const vector<Data>& v) {
		iter_.addDim(v.size());
	}
	void addFixed(const vector<Data>& v, uint i) {
		iter_.addFixed(v.size(), i);
	}

	void fix(uint i, Data d) {
		auto j = std::find(data_[i].begin(), data_[i].end(), d);
		if (j != data_[i].end()) {
			iter_[i] = j - data_[i].begin();
			iter_.fix(i);
		} else {
			assert(false && "element not found in CartesianMap vector");
		}
	}
	void unfix(uint i) { iter_.unfix(i); }

	void reset(bool drop_fixed = true) { iter_.reset(drop_fixed); }
	void makeNext() { iter_.makeNext(); }
	bool hasNext() const { return iter_.hasNext(); }
	uint size() const { return iter_.size(); }
	uint card() const { return iter_.card(); }
	Data operator[] (uint i) const {
		return data_[i][iter_[i]];
	}
	vector<Data> data() const {
		vector<Data> ret;
		for (uint i = 0; i < iter_.size(); ++ i) {
			ret.push_back(data_[i][iter_[i]]);
		};
		return ret;
	}

private:
	CartesianIter iter_;
	vector<vector<Data>> data_;
};

}}}
