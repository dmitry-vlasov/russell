#include "rus_prover_unify_index.hpp"

namespace mdl { namespace rus { namespace prover { namespace unify {

struct Normalizer {
	void normalize(RuleVar& rv) {
		if (rv.isVar() && rv.var.rep) {
			auto vi = vars.find(rv.var);
			if (vi == vars.end()) {
				uint c = 0;
				auto ti = types.find(rv.var.type);
				if (ti != types.end()) {
					c = ti->second + 1;
				}
				types[rv.var.type] = c;
				uint norm_v = Lex::toInt(Lex::toStr(rv.var.type->id()) + "_" + to_string(c));
				vars[rv.var] = norm_v;
				rv.var.lit = norm_v;
			} else {
				rv.var.lit = vi->second;
			}
		}
	}
	TermSubst normalize(const Term& t) {
		Term norm(t);
		for (auto& n : norm.nodes) {
			normalize(n.ruleVar);
		}
		Subst sub;
		for (const auto& p : vars) {
			sub.compose(p.second, Term(p.first));
		}
		return TermSubst(std::move(norm), std::move(sub));
	}

private:
	hmap<LightSymbol, uint, LightSymbol::Hash> vars;
	hmap<const Type*, uint> types;
};

void Index::add(const Term& t, uint val) {
	//cout << "to add: " << t0.show() << endl;
	//Term t = Normalizer().normalize(t0);
	//cout << "normalized: " << t.show() << endl;
	terms.emplace_back(t);
	endsInitialized = false;
	Node* n = &root_;
	Index::Iterator it;
	for (auto i = t.nodes.begin(); i != t.nodes.end(); ++i) {
		auto p = it;
		auto ni = n->nodes.emplace(i->ruleVar, Node()).first;
		n = &ni->second;
		it = ni;
		it->second.parent = p;
	}
	n->inds.push_back(size_);
	n->vals.push_back(val == -1 ? size_ : val);
	++size_;
}

void Index::verify(bool show) const {

	cout << "verifying index: START VERIFICATION" << endl;
	cout << show_pointers() << endl;

	vector<Iter> branch;
	if (root_.nodes.size()) {
		branch.emplace_back(root_);
		while (branch.size()) {
			Iter n = branch.back();
			for (auto e : n.iter()->second.ends) {

				if (show) {
					cout << "verifying end:" << (void*)&*e << endl;
				}

				bool endIsReacheable = false;
				Iter end = Iter(&n.iter()->second.nodes, e);
				Iter i = Iter(&n.iter()->second.nodes, e);
				deque<Iter> path;
				while (i.isValid()) {
					path.push_front(i);
					if (n == i) {
						endIsReacheable = true;
						break;
					}
					i = i.prev();
				}
				Iter p = n;
				if (show) {
					cout << "verifying path:" << endl;
				}
				for (uint i = 0; i < path.size(); ++ i) {
					Iter pi = path[i];

					if (show) {
						cout << pi.ruleVar().show() << "=(" << (void*)&*pi.iter() << ") ";
					}

					if (pi != p) {
						throw Error("pi != p, i: " + pi.show() + ", p: " + p.show());
					}
					if (i + 1 < path.size()) {
						auto next = p.node().nodes.find(path[i + 1].ruleVar());
						p = Iter(&p.node().nodes, next);
					}
				}
				if (!endIsReacheable) {
					throw Error("begin " + n.show() + " is not reacheable from end " + end.show());
				}
				if (show) {
					cout << endl;
				}
			}
			if (!n.isNextEnd()) {
				branch.push_back(n.next());
			} else {
				while (true) {
					branch.pop_back();
					if (!n.isSideEnd()) {
						branch.push_back(n.side());
						break;
					}
					if (branch.empty()) {
						break;
					}
					n = branch.back();
				}
			}
		}
	}
	cout << "verifying index: success" << endl;
	cout << show_pointers() << endl;
}

static void markup_ends(Index::Node& root, const Term& t) {
	struct NodePair {
		NodePair(Index::Iterator t, Term::ConstIterator e, uint l) : trie(t), end(e), len(l) { }
		Index::Iterator trie;
		Term::ConstIterator end;
		uint len;
	};
	stack<NodePair> st;
	Index::Node* n = &root;
	Index::Iterator it;
	for (auto i = t.nodes.begin(); i != t.nodes.end(); ++i) {
		auto p = it;
		auto ni = n->nodes.find(i->ruleVar);
		n = &ni->second;
		it = ni;
		st.emplace(ni, i->end, i->end - i);
		while (!st.empty() && st.top().end == i) {
			st.top().trie->second.ends.insert(ni);
			ni->second.lens.insert(st.top().len);
			st.pop();
		}
	}
}

static void markup_vars(Index::Node& n) {
	for (auto i = n.nodes.begin(); i != n.nodes.end(); ++i) {
		if (i->first.isVar()) {
			n.vars.insert(i);
		}
		markup_vars(i->second);
	}
}

void Index::initEnds() {
	for (const auto& term : terms) {
		markup_ends(root_, term);
	}
	markup_vars(root_);
	endsInitialized = true;
}

//#define VERIFY_TERM

static Term create_flatterm(const vector<Index::Iter>& branch) {
	Term ft(branch.size());
	for (uint i = 0; i < branch.size(); ++i) {
		ft.nodes[i].ruleVar = branch[i].iter()->first;
		for (uint len : branch[i].iter()->second.lens) {
			if (i >= len) {
				ft.nodes[i - len].end = ft.nodes.begin() + i;
			}
		}
	}
#ifdef VERIFY_TERM
	ft.verify();
#endif
	return ft;
}

Term Index::Iter::subTerm(ConstIterator i) const {
	vector<Iter> branch;
	ConstIterator start = i;
	while (i != ConstIterator()) {
		branch.emplace_back(nullptr, i);
		if (iter_ == i) {
			break;
		}
		i = i->second.parent;
	}
	std::reverse(branch.begin(), branch.end());
	return create_flatterm(branch);
}

string show_branch(const vector<Index::Iter>& branch) {
	string ret;
	for (const auto& i : branch) {
		ret += i.show() + " ";
	}
	return ret;
}

Index::Unpacked Index::unpack() const {
	return unpack(root_);
}

string Index::show() const {
	return show(root_);
}

string Index::show_pointers() const {
	vector<pair<vector<Iter>, uint>> vect;
	vector<Iter> branch;
	if (root_.nodes.size()) {
		branch.emplace_back(root_);
		while (branch.size()) {
			Iter n = branch.back();
			for (uint val : n.iter()->second.vals) {
				vect.emplace_back(branch, val);
			}
			if (!n.isNextEnd()) {
				branch.push_back(n.next());
			} else {
				while (true) {
					branch.pop_back();
					if (!n.isSideEnd()) {
						branch.push_back(n.side());
						break;
					}
					if (branch.empty()) {
						break;
					}
					n = branch.back();
				}
			}
		}
	}
	ostringstream oss;
	oss << "ROOT: " << (void*)&root_ << endl;
	for (const auto& p : vect) {
		for (const auto& i : p.first) {
			oss << i.ruleVar().show() << "=(" << (void*)&*i.iter() << ") ";
			oss << "ends=(";
			for (const auto& e : i.node().ends) {
				oss << (void*)&*e << " ";
			}
			oss << ") ";
		}
		oss << " --> " << p.second << "\n";
	}
	return oss.str();
}

Index::Unpacked Index::unpack(const Node& root) {
	return unpack(Iter(root));
}

Index::Unpacked Index::unpack(Iter root) {
	Unpacked ret;
	vector<Iter> branch;
	branch.emplace_back(root);
	while (branch.size()) {
		Iter n = branch.back();
		if (n.iter()->second.vals.size()) {
			ret.emplace_back(create_flatterm(branch), n.iter()->second.vals);
		}
		if (!n.isNextEnd()) {
			branch.push_back(n.next());
		} else {
			while (true) {
				branch.pop_back();
				if (!n.isSideEnd()) {
					branch.push_back(n.side());
					break;
				}
				if (branch.empty()) {
					break;
				}
				n = branch.back();
			}
		}
	}
	return ret;
}

string Index::show(Iter root) {
	string ret;
	for (const auto& p : unpack(root)) {
		ret += p.first.show() + " --> {";
		for (uint i : p.second) {
			ret += to_string(i) + " ";
		}
		ret += "}\n";
	}
	return ret;
}

string Index::show(const Node& root) {
	return show(Iter(root));
}

string Index::show_pointers(const Node& root) {
	vector<pair<vector<Iter>, uint>> vect;
	vector<Iter> branch;
	if (root.nodes.size()) {
		branch.emplace_back(root);
		while (branch.size()) {
			Iter n = branch.back();
			for (uint val : n.iter()->second.vals) {
				vect.emplace_back(branch, val);
			}
			if (!n.isNextEnd()) {
				branch.push_back(n.next());
			} else {
				while (true) {
					branch.pop_back();
					if (!n.isSideEnd()) {
						branch.push_back(n.side());
						break;
					}
					if (branch.empty()) {
						break;
					}
					n = branch.back();
				}
			}
		}
	}
	ostringstream oss;
	oss << "RELATIVE ROOT: " << (void*)&root << endl;
	for (const auto& p : vect) {
		for (const auto& i : p.first) {
			oss << i.ruleVar().show() << "=(" << (void*)&*i.iter() << ") ";
			oss << " ends=(";
			for (const auto& e : i.node().ends) {
				oss << (void*)&*e << " ";
			}
			oss << ") ";
		}
		oss << " --> " << p.second << "\n";
	}
	return oss.str();
}

uint Index::totalNodes() const {
	uint ret = 0;
	vector<Iter> branch;
	if (root().nodes.size()) {
		branch.emplace_back(root());
		while (branch.size()) {
			Iter n = branch.back();
			ret += n.iter()->second.vals.size();
			if (!n.isNextEnd()) {
				branch.push_back(n.next());
			} else {
				while (true) {
					branch.pop_back();
					if (!n.isSideEnd()) {
						branch.push_back(n.side());
						break;
					}
					if (branch.empty()) {
						break;
					}
					n = branch.back();
				}
			}
		}
	}
	return ret;
}

}}}}

