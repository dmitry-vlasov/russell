#include "rus_prover_unify_index.hpp"

namespace mdl { namespace rus { namespace prover { namespace unify {

void Index::add(const Term& t, uint val) {
	terms.emplace_back(t);
	endsInitialized = false;
	Node* n = &root_;
	Index::Iterator it;
	for (auto i = t.nodes.begin(); i != t.nodes.end(); ++i) {
		auto p = it;
		auto ni = n->map.emplace(i->ruleVar, Node()).first;
		n = &ni->second;
		it = ni;
		it->second.parent = p;
	}
	n->vals.push_back(val);
	++size_;
}

const vector<uint>* Index::find(const Term& t) const {
	const Node* n = &root();
	for (auto i = t.nodes.begin(); i != t.nodes.end(); ++i) {
		auto ni = n->map.find(i->ruleVar);
		if (ni == n->map.end()) {
			return nullptr;
		}
		n = &ni->second;
	}
	return &n->vals;
}

void Index::verify(bool show) const {

	cout << "verifying index: START VERIFICATION" << endl;
	cout << show_pointers() << endl;

	vector<Iter> branch;
	if (root().map.size()) {
		branch.emplace_back(root());
		while (branch.size()) {
			Iter n = branch.back();
			for (auto e : n.iter()->second.ends) {

				if (show) {
					cout << "verifying end:" << (void*)&*e << endl;
				}

				bool endIsReacheable = false;
				Iter end = Iter(&n.iter()->second, e);
				Iter i = Iter(&n.iter()->second, e);
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
						auto next = p.iter()->second.map.find(path[i + 1].ruleVar());
						p = Iter(p.node(), next);
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
		auto ni = n->map.find(i->ruleVar);
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
	for (auto i = n.map.begin(); i != n.map.end(); ++i) {
		if (i->first.isVar() && i->first.var.rep) {
			n.vars.insert(i);
		}
		markup_vars(i->second);
	}
}

void Index::initEnds() {
	for (const auto& t : terms) {
		markup_ends(root_, t);
	}
	markup_vars(root_);
	endsInitialized = true;
}

//#define VERIFY_TERM

static Term create_flatterm(const vector<Index::ConstIterator>& branch) {
	Term ft(branch.size());
	for (uint i = 0; i < branch.size(); ++i) {
		ft.nodes[i].ruleVar = branch[i]->first;
		for (uint len : branch[i]->second.lens) {
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
	vector<ConstIterator> branch;
	ConstIterator start = i;
	while (i != ConstIterator()) {
		branch.push_back(i);
		if (iter_ == i) {
			break;
		}
		i = i->second.parent;
	}
	std::reverse(branch.begin(), branch.end());
	try {
		return create_flatterm(branch);
	} catch (Error& err) {

		throw err;
	}
}

string show_branch(const vector<Index::Iter>& branch) {
	string ret;
	for (const auto& i : branch) {
		ret += i.show() + " ";
	}
	return ret;
}

Index::Unpacked Index::unpack() const {
	return unpack(root());
}

string Index::show() const {
	return show(root());
}

string Index::show_pointers() const {
	vector<pair<vector<Iter>, uint>> vect;
	vector<Iter> branch;
	if (root_.map.size()) {
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
			for (const auto& e : i.iter()->second.ends) {
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
	vector<ConstIterator> subterm;
	branch.emplace_back(root);
	while (branch.size()) {
		Iter n = branch.back();
		if (n.iter()->second.vals.size()) {
			subterm.reserve(branch.size());
			subterm.clear();
			for (auto i : branch) {
				subterm.push_back(i.iter());
			}
			ret.emplace_back(create_flatterm(subterm), n.iter()->second.vals);
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
	if (root.map.size()) {
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
			for (const auto& e : i.iter()->second.ends) {
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
	if (root().map.size()) {
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

