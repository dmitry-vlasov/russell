#include "rus_prover_cartesian.hpp"

namespace mdl { namespace rus { namespace prover {

void CartesianIter::addDim(uint d) {
	dims_.push_back(d);
	ind_.push_back(0);
}

void CartesianIter::addFixed(uint i) {
	dims_.push_back(-1);
	ind_.push_back(i);
}

void CartesianIter::makeNext() {
	for (uint i = 0; i < dims_.size(); ++ i) {
		if (dims_[i] == -1) {
			continue;
		}
		if (ind_[i] + 1 < dims_[i]) {
			++ ind_[i];
			return;
		} else {
			ind_[i] = 0;
		}
	}
	assert(false && "this execution point should be unreacheable");
}

string CartesianIter::show() const {
	string ret;
	ret += "size: " + to_string(dims_.size()) + ", ";
	ret += "dims: [";
	for (auto d : dims_) {
		ret += (d == -1 ? string("N") : to_string(d)) + " ";
	}
	ret += "]";
	return ret;
}
string CartesianIter::current() const {
	string ret = "[";
	for (auto i : ind_) {
		ret += to_string(i) + " ";
	}
	ret += "]";
	return ret;
}
bool CartesianIter::current_is(const vector<uint> ind) const {
	if (ind.size() != ind_.size()) return false;
	for (uint i = 0; i < ind.size(); ++ i) {
		if (ind[i] != ind_[i]) {
			return false;
		}
	}
	return true;
}
uint CartesianIter::cardinality() const {
	if (dims_.size() == 0) {
		return 0;
	}
	uint card = 1;
	for (uint i = 0; i < dims_.size(); ++ i) {
		if (dims_[i] != -1) {
			card *= dims_[i];
		}
	}
	return card;
}
bool CartesianIter::hasNext() const {
	for (uint i = 0; i < dims_.size(); ++ i) {
		if (dims_[i] != -1 && (ind_[i] + 1 != dims_[i])) {
			return true;
		}
	}
	return false;
}

}}}
