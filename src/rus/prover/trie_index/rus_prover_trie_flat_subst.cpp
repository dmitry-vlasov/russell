#include "rus_prover_trie_flat_subst.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

bool debug_flat_subst = false;
bool debug_flat_apply = false;

void FlatSubst::operator = (const FlatSubst& s) {
	ok = s.ok;
	if (ok) {
		for (const auto& p : s.sub) {
			sub.emplace(p.first, p.second);
		}
	}
}

void FlatSubst::operator = (FlatSubst&& s) {
	ok = s.ok;
	sub = std::move(s.sub);
	s.ok = true;
}

bool FlatSubst::operator == (const FlatSubst& s) const {
	if (ok != s.ok) {
		return false;
	}
	for (const auto& p : sub) {
		if (!s.maps(p.first)) {
			return false;
		}
		if (p.second != s.sub.at(p.first)) {
			return false;
		}
	}
	for (const auto& p : s.sub) {
		if (!maps(p.first)) {
			return false;
		}
		if (p.second != sub.at(p.first)) {
			return false;
		}
	}
	return true;
}

bool FlatSubst::operator != (const FlatSubst& s) const {
	return !operator ==(s);
}

void collect_vars(const FlatTerm& term, set<LightSymbol>& vars) {
	for (const auto& n : term.nodes) {
		if (n.ruleVar.isVar()) {
			vars.insert(n.ruleVar.var);
		}
	}
}

bool consistent(const FlatSubst* s, LightSymbol v, const FlatTerm& t) {
	set<LightSymbol> x_vars;
	collect_vars(t, x_vars);
	if (x_vars.find(v) != x_vars.end()) {
		return false;
	}
	auto j = s->sub.find(v);
	if (j != s->sub.end()) {
		if (t != j->second) {
			return false;
		}
	}
	for (LightSymbol y : x_vars) {
		auto i = s->sub.find(y);
		if (i != s->sub.end()) {
			set<LightSymbol> y_vars;
			collect_vars(i->second, y_vars);
			if (y_vars.find(v) != y_vars.end()) {
				return false;
			}
		}
	}
	return true;
}

bool FlatSubst::consistent(const FlatSubst& s) const {
	for (const auto& p : s.sub) {
		if (!trie_index::consistent(this, p.first, p.second)) {
			return false;
		}
	}
	return true;
}

void compose(FlatSubst& s1, const FlatSubst& s2, bool full) {
	static uint c = 0;
	++c;
	/*if (c == 105) {
		debug_flat_apply = true;
		debug_flatterm = true;
	} else {
		debug_flat_apply = false;
		debug_flatterm = false;
	}*/

	//cout << "(!!!) c = " << c << endl;

	if (debug_flat_subst) {
		cout << "-------------------------------------" << endl;
		cout << "c = " << c << endl;
		cout << "BEFORE " << (full ? "FULL" : "PART") << " COMPOSE THIS:" << endl;
		cout << Indent::paragraph(s1.show()) << endl;
		cout << "BEFORE COMPOSE S:" << endl;
		cout << Indent::paragraph(s2.show()) << endl;
	}
	FlatSubst ret;
	set<LightSymbol> vars;
	for (const auto& p : s1.sub) {
		FlatTerm ex = apply(s2, p.second);
		if (!(ex.kind() == FlatTerm::VAR && ex.var() == p.first)) {
			s1.sub[p.first] = ex; //std::move(ex);
			vars.insert(p.first);
		}
	}
	if (full) {
		for (const auto& p : s2.sub) {
			if (vars.find(p.first) == vars.end()) {
				s1.sub[p.first] = p.second;
			}
		}
	}
	if (debug_flat_subst) {
		cout << "AFTER COMPOSE THIS:" << endl;
		cout << Indent::paragraph(s1.show()) << endl;
		cout << "-------------------------------------" << endl;
	}
}

bool FlatSubst::compose(const FlatSubst& s, bool full) {
	if (!consistent(s)) {
		return false;
	}
	trie_index::compose(*this, s, full);
	return true;
}

bool FlatSubst::bicompose(const FlatSubst& s) {
	if (!s.consistent(*this)) {
		return false;
	}
	FlatSubst ss(s);
	trie_index::compose(ss, *this, false);
	if (!consistent(ss)) {
		return false;
	}
	trie_index::compose(*this, ss, true);
	return true;
}

bool FlatSubst::intersects(const FlatSubst& s) const {
	for (const auto& p : sub) {
		if (s.sub.count(p.first)) {
			return true;
		}
	}
	return false;
}

bool FlatSubst::composeable(const FlatSubst& s) const {
	set<LightSymbol> vars;
	for (const auto& p : sub) {
		collect_vars(p.second, vars);
	}
	for (const auto& p : s.sub) {
		if (vars.find(p.first) != vars.end()) {
			return true;
		}
	}
	return false;
}

string FlatSubst::show() const {
	string str;
	str += "OK = " + (ok ? string("TRUE") : string("FALSE")) + "\n";
	if (!sub.size()) {
		str += "empty\n";
	}
	for (const auto& p : sub) {
		str += prover::show(p.first) + " --> " + p.second.show() + "\n";
	}
	return str;
}

uint applied_len(const FlatSubst& s, const FlatTerm& t) {
	uint len = t.len();
	for (const auto& n : t.nodes) {
		if (n.ruleVar.isVar()) {
			auto it = s.sub.find(n.ruleVar.var);
			if (it != s.sub.end()) {
				len += it->second.len() - 1;
			}
		}
	}
	return len;
}

FlatTerm apply(const FlatSubst& s, const FlatTerm& t) {

	if (debug_flat_apply) {
		cout << "TO APPLY:" << endl;
		cout << "------------" << endl;
		cout << "SUB: " << endl << s.show() << endl;
		cout << "TERM: " << t.show() << endl;
	}

	uint len = 0;
	vector<uint> beg_shifts;
	vector<uint> end_shifts;
	vector<const FlatTerm*> subs;
	for (uint k = 0; k < t.len(); ++ k, ++ len) {
		const auto& n = t.nodes[k];
		beg_shifts.push_back(len);
		if (n.ruleVar.isVar()) {
			auto it = s.sub.find(n.ruleVar.var);
			if (it != s.sub.end()) {
				len += it->second.len() - 1;
				subs.push_back(&it->second);
			} else {
				subs.push_back(nullptr);
			}
		} else {
			subs.push_back(nullptr);
		}
		end_shifts.push_back(len);
	}

	if (debug_flat_apply) {
		cout << "BEG SHIFTS: [" << flush;
		for (uint k = 0; k < beg_shifts.size(); ++ k) {
			cout << k << " -> " << beg_shifts[k] << ", ";
		}
		cout << "]" << endl;
		cout << "END SHIFTS: [" << flush;
		for (uint k = 0; k < end_shifts.size(); ++ k) {
			cout << k << " -> " << end_shifts[k] << ", ";
		}
		cout << "]" << endl;
	}


	FlatTerm ret(len);
	for (uint k = 0; k < t.len(); ++ k) {
		if (subs[k]) {
			copyFlatSubTerm(&ret, beg_shifts[k], subs[k]->nodes.begin());
		} else {
			const auto& n = t.nodes[k];
			ret.nodes[beg_shifts[k]] = n;
			ret.nodes[beg_shifts[k]].end = ret.nodes.begin() + end_shifts[n.end - t.nodes.begin()];
		}
	}

	if (debug_flat_apply) {
		cout << "RET: " << ret.show() << endl;
		cout << "RET end - beg: " << (int)(ret.nodes[0].end - ret.nodes.begin()) << endl;
		cout << "------------" << endl << endl << endl;
	}

	return ret;
}
/*
FlatTerm apply(const FlatSubst& s, const FlatTerm& t) {
	uint length = applied_len(s, t);
	FlatTerm ret(length);
	uint i = 0;
	uint k = 0;
	vector<vector<uint>> begins(length);
	for (const auto& n : t.nodes) {
		bool substituted = false;
		if (n.ruleVar.isVar()) {
			auto it = s.sub.find(n.ruleVar.var);
			if (it != s.sub.end()) {
				copyFlatSubTerm(&ret, i, it->second.nodes.begin());
				for (uint beg : begins[i]) {
					ret.nodes[beg].end += (i + it->second.len() - k) - 1;
				}
				i += it->second.len();
				substituted = true;
			}
		}
		if (!substituted) {
			ret.nodes[i] = n;
			uint ind = n.end - t.nodes.begin();
			uint shifted_ind = ind + (i - k);
			begins[shifted_ind].push_back(i);
			ret.nodes[i].end = ret.nodes.begin() + shifted_ind;
			i += 1;
		}
		k += 1;
	}
	if (debug_flat_apply) {
		cout << "APPLY:" << endl;
		cout << "------------" << endl;
		cout << "applied_len(s, t): " << applied_len(s, t) << endl;
		cout << "SUB: " << endl << s.show() << endl;
		cout << "TERM: " << t.show() << endl;
		cout << "RET: " << ret.show() << endl;
		cout << "RET end - beg: " << (int)(ret.nodes[0].end - ret.nodes.begin()) << endl;
		cout << "------------" << endl << endl << endl;
	}

	return ret;
}*/

FlatSubst compose(const FlatSubst& s1, const FlatSubst& s2) {
	FlatSubst ret(s1);
	ret.compose(s2);
	return ret;
}

bool composable(const FlatSubst& s1, const FlatSubst& s2) {
	for (const auto& p : s1.sub) {
		if (s2.sub.find(p.first) != s2.sub.end()) {
			return true;
		}
	}
	return false;
}

FlatSubst convert2flatsubst(const Subst& s) {
	FlatSubst ret;
	for (const auto& p : s.sub) {
		ret.sub.emplace(p.first, std::move(convert2flatterm(p.second)));
	}
	return ret;
}

Subst convert2subst(const FlatSubst& s) {
	Subst ret;
	for (const auto& p : s.sub) {
		ret.sub.emplace(p.first, std::move(convert2lighttree(p.second)));
	}
	return ret;
}

}}}}
