#include <rus_ast.hpp>

namespace mdl { namespace rus {

struct SymbInfo {
	SymbInfo(uint o, const Type* t, uint l, bool e, uint i) :
		orig(o), type(t), lit(l), exclamation(e), ind(i) { }
	bool operator < (const SymbInfo& si) const {
		return orig < si.orig;
	}
	string show() const {
		ostringstream oss;
		oss << "orig: " << Lex::toStr(orig) << ", lit: " << Lex::toStr(lit) << ", excl: " << (exclamation ? "T" : "F") << ", ind: " << ind;
		return oss.str();
	}
	/*VarTree beautify() const {
		string orig_lit = Lex::toStr(lit);
		uint new_ind =
			exclamation ?
			excl_reindex.at(lit).at(ind) :
			norm_reindex.at(lit).at(ind);
		string new_lit =
			orig_lit + (si.exclamation ? "'" : "") +
			(new_ind == 0 ? "" : "_" + to_string(new_ind));
		return VarTree()
	}*/
	uint orig;
	const Type* type;
	uint lit;
	bool exclamation;
	uint ind;
};

SymbInfo symb_info(uint orig, const Type* type) {
	string str = Lex::toStr(orig);
	string::size_type excl_pos = str.rfind('!');
	string::size_type under_pos = str.rfind('_');
	uint ind = -1;
	if (under_pos != string::npos) {
		string numb = str.substr(under_pos + 1);
		try {
			ind = stoi(numb);
		} catch (std::invalid_argument&) { }
	}
	bool excl =
		(excl_pos != string::npos) &&
		(under_pos != string::npos) &&
		(under_pos == excl_pos + 1);
	string lit_str =
		excl ? str.substr(0, excl_pos) :
		(under_pos == string::npos ? str : str.substr(0, under_pos));
	return SymbInfo(orig, type, Lex::toInt(lit_str), excl, ind);
}

map<uint, SymbInfo> collect_vars_info(const rus::Expr& ex) {
	map<uint, SymbInfo> ret;
	for (auto& s : ex.symbols) {
		if (Var* v = dynamic_cast<Var*>(s.get())) {
			ret.emplace(v->lit(), symb_info(v->lit(), v->type()));
		}
	}
	return ret;
}

map<uint, SymbInfo> collect_vars_info(const rus::Assertion& ass) {
	map<uint, SymbInfo> ret;
	for (auto& h : ass.hyps) {
		ret = std::move(maps_union(ret, collect_vars_info(h->expr)));
	}
	ret = std::move(maps_union(ret, collect_vars_info(ass.prop->expr)));
	return ret;
}

void optimize_exclamation(map<uint, SymbInfo>& si_map) {
	const SymbInfo* first_si = nullptr;
	bool excl_the_same = true;
	for (auto& p : si_map) {
		if (!first_si) {
			first_si = &p.second;
		}
		if (first_si->exclamation != p.second.exclamation) {
			excl_the_same = false;
			break;
		}
	}
	if (excl_the_same) {
		for (auto& p : si_map) {
			p.second.exclamation = false;
		}
	}
}

Substitution optimize_inds(const map<uint, SymbInfo>& symb_info) {
	map<uint, set<int>> collected_norm;
	map<uint, set<int>> collected_excl;
	for (auto& p : symb_info) {
		const SymbInfo& si = p.second;
		if (si.exclamation) {
			collected_excl[si.lit].insert(si.ind);
		} else {
			collected_norm[si.lit].insert(si.ind);
		}
	}
	map<uint, map<uint, uint>> norm_reindex;
	for (auto& p : collected_norm) {
		map<uint, uint> reindex;
		uint i = 0;
		for (uint k : p.second) {
			reindex.emplace(k, i++);
		}
		norm_reindex.emplace(p.first, std::move(reindex));
	}
	map<uint, map<uint, uint>> excl_reindex;
	for (auto& p : collected_excl) {
		map<uint, uint> reindex;
		uint i = 0;
		for (uint k : p.second) {
			reindex.emplace(k, i++);
		}
		excl_reindex.emplace(p.first, std::move(reindex));
	}
	auto mult_prime = [](int n) { string ret; while (n--) ret += "'"; return ret; };
	Substitution ret;
	for (auto& p : symb_info) {
		uint orig = p.first;
		const SymbInfo& si = p.second;
		uint optimized = -1;
		string orig_lit = Lex::toStr(si.lit);
		uint new_ind =
			si.exclamation ?
			excl_reindex.at(si.lit).at(si.ind) :
			norm_reindex.at(si.lit).at(si.ind);
		string new_lit =
			orig_lit + (si.exclamation ? "*" : "") +
			mult_prime(new_ind);
		ret.join(orig, si.type, VarTree(Lex::toInt(new_lit), si.type));
	}
	return ret;
}

void beautify(Assertion& a) {
	map<uint, SymbInfo> si_map = collect_vars_info(a);
	optimize_exclamation(si_map);
	Substitution opt_inds = optimize_inds(si_map);
	for (auto& h : a.hyps) {
		h->expr = std::move(apply(opt_inds, h->expr));
	}
	//cout << "SUBST: " << endl << opt_inds.show() << endl;
	a.prop->expr = std::move(apply(opt_inds, a.prop->expr));
	if (Theorem* th = dynamic_cast<Theorem*>(&a)) {
		traverseProof(th->proof->qed->step,[&opt_inds](Writable* w) {
			if (Step* step = dynamic_cast<Step*>(w)) {
				step->expr = std::move(apply(opt_inds, step->expr));
			}
		});
		complete_proof_vars(th->proof.get());
	}
	complete_assertion_vars(&a);

	//cout << "BEAUTIFIED:" << endl;
	//cout << a << endl;

	if (Theorem* th = dynamic_cast<Theorem*>(&a)) {
		th->proof->verify(VERIFY_ALL, &th->disj);
	}
}

}}
