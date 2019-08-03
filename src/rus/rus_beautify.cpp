#include <rus_ast.hpp>

namespace mdl { namespace rus {

struct SymbInfo {
	SymbInfo(uint o, const Type* t, uint l, uint i) :
		orig(o), type(t), lit(l), ind(i) { }
	bool operator < (const SymbInfo& si) const {
		return orig < si.orig;
	}
	string show() const {
		ostringstream oss;
		oss << "orig: " << Lex::toStr(orig) << ", lit: " << Lex::toStr(lit) << ", ind: " << ind;
		return oss.str();
	}
	uint orig;
	const Type* type;
	uint lit;
	uint ind;
};

SymbInfo symb_info(uint orig, const Type* type) {
	string str = Lex::toStr(orig);
	string::size_type under_pos = str.rfind('_');
	uint ind = -1;
	if (under_pos != string::npos) {
		string numb = str.substr(under_pos + 1);
		try {
			ind = stoi(numb);
			str = str.substr(0, under_pos);
		} catch (std::invalid_argument&) { }
	}
	return SymbInfo(orig, type, Lex::toInt(str), ind);
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

map<uint, SymbInfo> collect_vars_info(const rus::Proof& proof) {
	map<uint, SymbInfo> ret;
	for (auto& s : proof.steps) {
		ret = std::move(maps_union(ret, collect_vars_info(s->expr)));
	}
	return ret;
}

map<uint, SymbInfo> collect_vars_info(const rus::Assertion& ass) {
	map<uint, SymbInfo> ret;
	for (auto& h : ass.hyps) {
		ret = std::move(maps_union(ret, collect_vars_info(h->expr)));
	}
	ret = std::move(maps_union(ret, collect_vars_info(ass.prop->expr)));
	if (const Theorem* th = dynamic_cast<const Theorem*>(&ass)) {
		if (th->proof) {
			ret = std::move(maps_union(ret, collect_vars_info(*th->proof)));
		}
	}
	return ret;
}

Substitution optimize_inds(const map<uint, SymbInfo>& symb_info) {
	map<uint, set<int>> collected;
	for (auto& p : symb_info) {
		const SymbInfo& si = p.second;
		if (si.ind != -1) {
			collected[si.lit].insert(si.ind);
		}
	}
	map<uint, map<uint, uint>> reindex;
	for (auto& p : collected) {
		map<uint, uint> m;
		uint i = 0;
		for (uint k : p.second) {
			m.emplace(k, i++);
		}
		reindex.emplace(p.first, std::move(m));
	}
	auto mult_prime = [](int n) { string ret; while (n--) ret += "'"; return ret; };
	Substitution ret;
	for (auto& p : symb_info) {
		const SymbInfo& si = p.second;
		if (si.ind != -1) {
			uint orig = p.first;
			uint optimized = -1;
			string orig_lit = Lex::toStr(si.lit);
			uint new_ind = reindex.at(si.lit).at(si.ind);
			string new_lit = orig_lit + mult_prime(new_ind);
			ret.join(orig, si.type, VarTree(Lex::toInt(new_lit), si.type));
		}
	}
	return ret;
}



















void raw_vars(const rus::Expr& ex, set<uint>& r) {
	for (auto& s : ex.symbols) {
		if (Var* v = dynamic_cast<Var*>(s.get())) {
			const string& str = Lex::toStr(v->lit());
			if (std::min(str.find('_'), str.find('\'')) == string::npos) {
				r.insert(v->lit());
			}
		}
	}
}

void raw_vars(const rus::Assertion& ass, set<uint>& r) {
	for (auto& h : ass.hyps) {
		raw_vars(h->expr, r);
	}
	raw_vars(ass.prop->expr, r);
	if (const Theorem* th = dynamic_cast<const Theorem*>(&ass)) {
		if (th->proof) {
			for (auto& s : th->proof->steps) {
				raw_vars(s->expr, r);
			}
		}
	}
}


void make_sub(uint orig, const Type* type, Substitution& sub, map<uint, uint>& m, const set<uint>& r) {
	if (!sub.maps(orig)) {
		string str = Lex::toStr(orig);
		string::size_type pos = std::min(str.find('_'), str.find('\''));
		if (pos != string::npos) {
			string prefix = str.substr(0, pos);
			uint prefix_id = Lex::toInt(prefix);
			if (!m.count(prefix_id)) {
				if (r.count(prefix_id)) {
					m.emplace(prefix_id, 1);
				} else {
					m.emplace(prefix_id, 0);
				}
			} else {
				++m[prefix_id];
			}
			auto mult_prime = [](int n) { string ret; while (n--) ret += "'"; return ret; };
			uint image = Lex::toInt(prefix + mult_prime(m.at(prefix_id)));
			sub.join(orig, type, VarTree(image, type));
		}
	}
}

void make_sub(const rus::Expr& ex, Substitution& sub, map<uint, uint>& m, const set<uint>& r) {
	for (auto& s : ex.symbols) {
		if (Var* v = dynamic_cast<Var*>(s.get())) {
			make_sub(v->lit(), v->type(), sub, m, r);
		}
	}
}

void make_sub(const rus::Assertion& ass, Substitution& sub, map<uint, uint>& m, const set<uint>& r) {
	for (auto& h : ass.hyps) {
		make_sub(h->expr, sub, m, r);
	}
	make_sub(ass.prop->expr, sub, m, r);
	if (const Theorem* th = dynamic_cast<const Theorem*>(&ass)) {
		if (th->proof) {
			for (auto& s : th->proof->steps) {
				make_sub(s->expr, sub, m, r);
			}
		}
	}
}

void beautify(Assertion& a) {
	//map<uint, SymbInfo> si_map = collect_vars_info(a);
	//Substitution opt_inds = optimize_inds(si_map);
	set<uint> raw;
	raw_vars(a, raw);
	Substitution opt_inds;
	map<uint, uint> m;
	make_sub(a, opt_inds, m, raw);
	for (auto& h : a.hyps) {
		h->expr = std::move(apply(opt_inds, h->expr));
	}
	//cout << "ORIG:" << endl;
	//cout << a << endl;
	//cout << "SUBST: " << endl << opt_inds.show() << endl;
	a.prop->expr = std::move(apply(opt_inds, a.prop->expr));
	complete_assertion_vars(&a);
	if (Theorem* th = dynamic_cast<Theorem*>(&a)) {
		traverseProof(th->proof->qed->step,[&opt_inds](Writable* w) {
			if (Step* step = dynamic_cast<Step*>(w)) {
				step->expr = std::move(apply(opt_inds, step->expr));
			}
		});
		complete_proof_vars(th->proof.get());
	}
	if (Theorem* th = dynamic_cast<Theorem*>(&a)) {
		th->verify();
	}

	//cout << "BEAUTIFIED:" << endl;
	//cout << a << endl;
	//exit(0);
}

}}
