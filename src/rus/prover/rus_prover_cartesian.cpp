#include "rus_prover_cartesian.hpp"

namespace mdl { namespace rus { namespace prover {

CartesianIter::CartesianIter(const vector<uint>& dims) {
	for (auto& d : dims) {
		dims_.emplace_back(d);
	}
}

void CartesianIter::incDim() {
	++ dims_[dims_.size() - 1].size;
}

void CartesianIter::incSize() {
	dims_.emplace_back();
}

void CartesianIter::addDim(uint d) {
	dims_.emplace_back(d);
}

void CartesianIter::addFixed(uint d, uint i) {
	dims_.emplace_back(d, i, Dim::FIXED);
}

void CartesianIter::reset(bool drop_kind) {
	for (auto& d : dims_) {
		if (drop_kind) {
			d.kind = Dim::NORM;
		}
		if (d.kind == Dim::NORM) {
			d.ind = 0;
		}
	}
}

void CartesianIter::makeNext() {
	for (auto& d : dims_) {
		if (d.kind != Dim::NORM) {
			continue;
		}
		if (d.ind + 1 < d.size) {
			++ d.ind;
			return;
		} else {
			d.ind = 0;
		}
	}
	cout << show() << endl;
	assert(false && "this execution point should be unreacheable");
}

vector<uint> CartesianIter::inds() const {
	vector<uint> ret;
	for (const auto& d : dims_) {
		ret.push_back(d.ind);
	}
	return ret;
}

string CartesianIter::show() const {
	string ret;
	ret += "size: " + to_string(dims_.size()) + ", ";
	ret += "dims: [";
	for (const auto& d : dims_) {
		switch (d.kind) {
		case Dim::FIXED:   ret += "(fixed)";   break;
		case Dim::SKIPPED: ret += "(skipped)"; break;
		default: break;
		}
		ret += to_string(d.size) + " ";
	}
	ret += "]";
	return ret;
}
string CartesianIter::current() const {
	string ret = "[";
	for (const auto& d : dims_) {
		ret += to_string(d.ind) + " ";
	}
	ret += "]";
	return ret;
}
bool CartesianIter::current_is(const vector<uint> ind) const {
	if (dims_.size() != ind.size()) return false;
	for (uint i = 0; i < ind.size(); ++ i) {
		if (ind[i] != dims_[i].ind) {
			return false;
		}
	}
	return true;
}
uint CartesianIter::card() const {
	uint active_dims = 0;
	for (auto& d : dims_) {
		if (d.kind != Dim::SKIPPED) {
			++active_dims;
		}
	}
	if (active_dims == 0) {
		return 0;
	}
	uint card = 1;
	for (auto& d : dims_) {
		switch (d.kind) {
		case Dim::NORM:    card *= d.size; break;
		case Dim::FIXED:   card *= (d.size > 0) ? 1 : 0; break;
		case Dim::SKIPPED: break;
		}
	}
	return card;
}
bool CartesianIter::hasNext() const {
	for (auto& d : dims_) {
		if (d.kind == Dim::NORM && (d.ind + 1 != d.size)) {
			return true;
		}
	}
	return false;
}

}}}
