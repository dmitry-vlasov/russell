#include "rus_prover_cartesian.hpp"

namespace mdl { namespace rus { namespace prover {

CartesianIter::CartesianIter(const vector<uint>& d) :
	dims_(d), fixed_(d.size()), ind_(d.size()) {
	for (uint i = 0; i < dims_.size(); ++ i) {
		fixed_[i] = false;
		ind_[i] = 0;
	}
}

void CartesianIter::incDim() {
	++ dims_[dims_.size() - 1];
}

void CartesianIter::incSize() {
	dims_.push_back(0);
	fixed_.push_back(false);
	ind_.push_back(0);
}

void CartesianIter::addDim(uint d) {
	dims_.push_back(d);
	fixed_.push_back(false);
	ind_.push_back(0);
}

void CartesianIter::addFixed(uint d, uint i) {
	dims_.push_back(d);
	fixed_.push_back(true);
	ind_.push_back(i);
}

void CartesianIter::reset(bool drop_fixed) {
	for (uint i = 0; i < dims_.size(); ++ i) {
		if (drop_fixed) {
			fixed_[i] = false;
		}
		if (!fixed_[i]) {
			ind_[i] = 0;
		}
	}
}

void CartesianIter::makeNext() {
	for (uint i = 0; i < dims_.size(); ++ i) {
		if (fixed_[i]) {
			continue;
		}
		if (ind_[i] + 1 < dims_[i]) {
			++ ind_[i];
			return;
		} else {
			ind_[i] = 0;
		}
	}
	cout << show() << endl;
	assert(false && "this execution point should be unreacheable");
}

string CartesianIter::show() const {
	string ret;
	ret += "size: " + to_string(dims_.size()) + ", ";
	ret += "dims: [";
	for (uint i = 0; i < dims_.size(); ++ i) {
		ret += (fixed_[i] ? string("(fixed)") : "") + to_string(dims_[i]) + " ";
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
uint CartesianIter::card() const {
	if (dims_.size() == 0) {
		return 0;
	}
	uint card = 1;
	for (uint i = 0; i < dims_.size(); ++ i) {
		if (!fixed_[i]) {
			card *= dims_[i];
		}
	}
	return card;
}
bool CartesianIter::hasNext() const {
	for (uint i = 0; i < dims_.size(); ++ i) {
		if (!fixed_[i] && (ind_[i] + 1 != dims_[i])) {
			return true;
		}
	}
	return false;
}

}}}
