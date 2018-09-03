#include "rus_prover_space.hpp"
#include "rus_prover_unify.hpp"

namespace mdl { namespace rus { namespace prover {

struct CartesianIter {
	struct Dim {
		enum Kind { NORM, FIXED, SKIPPED };
		Dim(uint s = 0, uint i = 0, Kind k = NORM) :
			size(s), ind(i), kind(k) { }
		Dim(const Dim&) = default;
		Dim& operator = (const Dim&) = default;
		bool carriesData() const {
			return kind != SKIPPED && size > 0;
		}

		uint size;
		uint ind;
		Kind kind;
	};

	CartesianIter() = default;
	CartesianIter(const vector<uint>&);
	CartesianIter(const CartesianIter&) = default;

	CartesianIter& operator =(const CartesianIter&) = default;

	void incDim(uint i = -1);
	void incSize();

	void addDim(uint d);
	void addFixed(uint d, uint i);
	void addSkipped(uint d);

	void fix(uint d, uint i) {
		dims_[d].kind = Dim::FIXED;
		dims_[d].ind = i;
	}
	void skip(uint d) {
		dims_[d].kind = Dim::SKIPPED;
		dims_[d].ind = -1;
	}
	void norm(uint d) {
		dims_[d].kind = Dim::NORM;
		dims_[d].ind = 0;
	}

	void reset(bool drop_kind = true);
	void makeNext();
	bool hasNext() const;
	uint size() const { return dims_.size(); }
	uint card() const;
	uint activeSize() const;
	uint operator[] (uint i) const { return dims_[i].ind; }
	uint& operator[] (uint i) { return dims_[i].ind; }
	Dim get(uint i) const { return dims_[i]; }
	vector<uint> inds() const;

	string show() const;
	string current() const ;
	bool current_is(const vector<uint> ind) const;

private:
	vector<Dim> dims_;
};

template<class Data>
struct CartesianProd {
	CartesianProd() = default;
	CartesianProd(const vector<vector<Data>>& d) : data_(d) {
		for (const auto& v : data_) {
			addDim(v.size());
		}
	}
	CartesianProd(const CartesianProd&) = default;

	CartesianProd& operator = (const CartesianProd&) = default;

	void incDim(Data d, uint i = -1) {
		if (i == -1) {
			data_[data_.size() - 1].push_back(d);
		} else {
			data_[i].push_back(d);
		}
		iter_.incDim(i);
	}
	void incSize() {
		data_.push_back(vector<Data>());
		iter_.incSize();
	}

	void addDim(const vector<Data>& v, uint i = -1) {
		uint ind = (i == -1) ? data_.size() - 1 : i;
		for (auto d : v) {
			data_[ind].push_back(d);
			iter_.incDim();
		}
	}
	void addFixed(const vector<Data>& v, uint i) {
		for (auto d : v) {
			data_[i].push_back(d);
		}
		iter_.addFixed(v.size(), i);
	}
	CartesianIter::Dim getDim(uint i) const { return iter_.get(i); }

	void fix(uint i, Data d) {
		auto j = std::find(data_[i].begin(), data_[i].end(), d);
		if (j != data_[i].end()) {
			iter_.fix(i, j - data_[i].begin());
		} /*else {
			assert(false && "element not found in CartesianMap vector");
		}*/
	}
	void skip(uint i) { iter_.skip(i); }
	void norm(uint i) { iter_.norm(i); }

	void reset(bool drop_fixed = true) { iter_.reset(drop_fixed); }
	void makeNext() { iter_.makeNext(); }
	bool hasNext() const { return iter_.hasNext(); }
	uint size() const { return iter_.size(); }
	uint card() const { return iter_.card(); }
	uint activeSize() const { return iter_.activeSize(); }
	const CartesianIter& iter() const { return iter_; }

	vector<Data> data() const {
		vector<Data> ret;
		for (uint i = 0; i < iter_.size(); ++ i) {
			if (iter_.get(i).carriesData()) {
				ret.push_back(data_[i][iter_[i]]);
			}
		}
		return ret;
	}

	vector<uint> indexes() const {
		vector<uint> ret;
		for (uint i = 0, c = 0; i < iter_.size(); ++ i) {
			ret.push_back(iter_.get(i).carriesData() ? c++ : -1);
		}
		return ret;
	}
	string show() const {
		ostringstream oss;
		oss << "iter: " << iter_.show() << endl;
		oss << "curr: " << iter_.current() << endl;
		oss << "data: " << endl;
		for (const vector<Data>& v : data_) {
			for (const Data& d : v) {
				oss << "\t" << d << ", ";
			}
			oss << endl;
		}
		return oss.str();
	}

private:
	CartesianIter iter_;
	vector<vector<Data>> data_;
};

struct PowerSetIter {
	void addDim() { iter_.addDim(2); }
	void addFixed(bool v) { iter_.addFixed(2, v ? 1 : 0); }
	void addSkipped() { iter_.addSkipped(2); }

	void makeNext() { iter_.makeNext(); }
	bool hasNext() const { return iter_.hasNext(); }
	uint size() const { return iter_.size(); }
	uint card() const { return iter_.card(); }
	bool operator[] (uint i) const { return iter_[i] == 1; }
	vector<bool> values() const {
		vector<bool> ret;
		for (uint i = 0; i < iter_.size(); ++ i) {
			ret.push_back(iter_[i] == 1);
		}
		return ret;
	}

	string show() const {
		string ret;
		ret += "[";
		for (uint i = 0; i < iter_.size(); ++ i) {
			if (i > 0) {
				ret += ", ";
			}
			ret += (iter_[i] == 1) ? "T" : "F";
		}
		ret += "]";
		return ret;
	}

private:
	CartesianIter iter_;
};


}}}
