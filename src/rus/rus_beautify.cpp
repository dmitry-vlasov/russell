#include <rus_ast.hpp>

namespace mdl { namespace rus {

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
		traverseProof(th->proof->qed(),[&opt_inds](Writable* w) {
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
}

}}
