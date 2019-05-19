#pragma once

#include "../rus_prover_multy_subst.hpp"
#include "../rus_prover_node.hpp"

namespace mdl { namespace rus { namespace prover { namespace unify {

struct Index {
	struct Node {
		struct NodeIterLess {
			bool operator () (map<RuleVar, Node>::const_iterator i1, map<RuleVar, Node>::const_iterator i2) const {
				return &*i1 < &*i2;
			}
		};
		map<RuleVar, Node>::iterator parent;
		vector<uint> vals;
		map<RuleVar, Node> nodes;

		set<map<RuleVar, Node>::const_iterator, NodeIterLess> ends; // All ends of terms, which start at current node
		set<map<RuleVar, Node>::const_iterator, NodeIterLess> vars; // All variables among nodes
		set<uint> lens;
	};
	typedef map<RuleVar, Node>::iterator Iterator;
	typedef map<RuleVar, Node>::const_iterator ConstIterator;
	typedef map<uint, Subst> Unified;
	typedef vector<pair<Term, vector<uint>>> Unpacked;
	struct Iter;

	void add(const Term& t, uint val);
	Unpacked unpack() const;
	string show() const;
	string show_pointers() const;

	static Unpacked unpack(const Node&);
	static Unpacked unpack(Iter);
	static string show(const Node&);
	static string show(Iter);
	static string show_pointers(const Node&);

	uint totalNodes() const;
	bool empty() const { return root_.nodes.empty(); }
	void verify(bool show = false) const;

	uint size() const { return size_; }
	const Node& root() const {
		if (!endsInitialized) {
			const_cast<Index*>(this)->initEnds();
		}
		return root_;
	}

private:
	void initEnds();
	uint size_ = 0;
	Node root_;
	bool endsInitialized = false;
	vector<Term> terms;
};

struct Index::Iter {
	Iter() : valid_(false), node_(nullptr) { }
	Iter(const Node& n) : valid_(true), iter_(n.nodes.begin()), node_(&n) { }
	Iter(const Node* n, ConstIterator i) : valid_(i != ConstIterator()), iter_(i), node_(n) { }
	Iter(const Node* n, ConstIterator i, bool v) : valid_(v && i != ConstIterator()), iter_(i), node_(n) { }
	Iter(const Iter&) = default;
	Iter& operator = (const Iter&) = default;
	bool operator == (const Iter& i) const {
		return iter_ == i.iter_;
	}
	bool operator != (const Iter& i) const {
		return !operator ==(i);
	}
	void setHint(const Rule* r) {
		hint_ = r;
	}
	Iter side() const {
		if (hint_) {
			Iter i(*this);
			while (true) {
				i = i.elementarySide();
				if (!i.isValid() || i.isVar() || i.ruleVar().rule == hint_) {
					break;
				}
			}
			return i;
		} else {
			return elementarySide();
		}
	}
	Iter next() const {
		if (!valid_ || isNextEnd()) {
			return Iter(nullptr, iter_, false);
		} else {
			return Iter(&iter_->second, iter_->second.nodes.begin());
		}
	}
	Iter prev() const {
		return Iter(nullptr, iter_->second.parent);
	}
	Iter reset() const {
		return Iter(node_, node_->nodes.begin(), valid_);
	}
	bool isNextEnd() const {
		return iter_->second.nodes.size() == 0;
	}
	bool isSideEnd() const {
		return !side().isValid();
	}
	bool isValid() const { return valid_; }
	ConstIterator iter() const {
		if (!valid_) {
			throw Error("Not valid Index::Iter");
		}
		return iter_;
	}
	Term subTerm(ConstIterator) const;
	Term subTerm(const Iter& i) const {
		return subTerm(i.iter_);
	}

	vector<pair<Term, Iter>> subTerms() const {
		vector<pair<Term, Iter>> ret;
		ret.reserve(iter_->second.ends.size());
		for (auto end : iter_->second.ends) {
			ret.emplace_back(subTerm(end), Iter(&iter_->second, end));
		}
		return ret;
	}
	vector<Iter> ends() const {
		vector<Iter> ret;
		ret.reserve(iter_->second.ends.size());
		for (auto end : iter_->second.ends) {
			ret.emplace_back(&iter_->second, end);
		}
		return ret;
	}
	vector<Iter> vars() const {
		vector<Iter> ret;
		ret.reserve(iter_->second.vars.size());
		for (auto var : iter_->second.vars) {
			ret.emplace_back(&iter_->second, var);
		}
		return ret;
	}
	bool isEnd(const Iter& i) const {
		return iter_->second.ends.find(i.iter()) != iter_->second.ends.end();
	}
	bool isVar() const {
		return iter_->first.isVar() && iter_->first.var.rep;
	}
	LightSymbol var() const {
		return iter_->first.var;
	}
	RuleVar ruleVar() const {
		return iter_->first;
	}
	string show(bool full = false) const {
		ostringstream oss;
			if (full) {
			oss << "iter: " << ((iter_ == ConstIterator()) ? "<>" : iter_->first.show()) << " =(" << (void*)&*iter_ << ") " << "\n";
			if (iter_->second.ends.size()) {
				oss << "ends: ";
				for (auto i : iter_->second.ends) {
					oss << (void*)&*i << " ";
				}
				oss << "\n";
			}
			if (iter_->second.vals.size()) {
				oss << "vals: ";
				for (uint val : iter_->second.vals) {
					oss << val << " ";
				}
				oss << "\n";
			}
			oss << "\n";
		} else {
			oss << ((iter_ == ConstIterator()) ? "<>" : iter_->first.show()) << "=(" << (void*)&*iter_ << ") " ;
			if (iter_->second.vals.size()) {
				oss << "[";
				for (uint val : iter_->second.vals) {
					oss << val << " ";
				}
				oss << "]";
			}
		}
		return oss.str();
	}
	string showBranch(bool full = false) const {
		vector<Iter> branch;
		Iter i = *this;
		while (i.isValid()) {
			branch.push_back(i);
			i = i.prev();
		}
		std::reverse(branch.begin(), branch.end());
		string ret;
		for (auto it : branch) {
			ret += it.show(full);
		}
		return ret;
	}
	string showTree() const {
		return Index::show(*this);
	}
	const Node* node() const {
		return node_;
	}

private:
	bool isElementarySideEnd() const {
		if (!valid_) {
			return true;
		} else {
			auto i = iter_;
			return ++i == node_->nodes.end();
		}
	}
	Iter elementarySide() const {
		if (!valid_ || isElementarySideEnd()) {
			return Iter(nullptr, iter_, false);
		} else {
			auto i = iter_;
			return Iter(node_, ++i, true);
		}
	}
	bool valid_;
	ConstIterator iter_;
	const Node* node_;
	const Rule* hint_ = nullptr;
};

struct Normalizer {
	Normalizer(const Term& t) : normalized(t) {
		for (auto& n : normalized.nodes) {
			normalize(n.ruleVar);
		}
	}

	VarRepl norm;
	VarRepl denorm;
	Term normalized;

private:
	void normalize(RuleVar& rv) {
		if (rv.isVar() && rv.var.rep) {
			uint v = rv.var.lit;
			uint norm_v = norm.replace(v);
			if (norm_v == -1) {
				uint c = 0;
				auto ti = types.find(rv.var.type);
				if (ti != types.end()) {
					c = ti->second + 1;
				}
				types[rv.var.type] = c;
				norm_v = Lex::toInt(Lex::toStr(rv.var.type->id()) + "_" + to_string(c));
				norm.addReplacement(v, norm_v);
				denorm.addReplacement(norm_v, v);
				rv.var.lit = norm_v;
			} else {
				rv.var.lit = norm_v;
			}
		}
	}
	hmap<const Type*, uint> types;
};

map<uint, TermSubst> unify_index_term(const Index& ind, const Term& term);

template<class Data>
struct IndexMap {
	struct Unified {
		Unified(const Data& d, Subst&& s) : data(d), sub(std::move(s)) { }
		Unified(const Unified&) = default;
		Unified(Unified&&) = default;
		Data data;
		Subst sub;
	};
	void add(const Term& t, const Data& d) {
		Normalizer n(t);
		index_.add(n.normalized, stored_.size());
		stored_.emplace_back(d, std::move(n.denorm));
	}
	string show() const {
		vector<pair<Term, uint>> terms = index_.unpack();
		if (!terms.size()) {
			return "\n";
		} else {
			string ret;
			for (const auto&  p : terms) {
				Data d = stored_[p.second].data;
				ret += "[" + p.first.show() + "]" + " -> " + to_string(p.second) + "\n";
			}
			return ret;
		}
	}
	string show_pointers() const {
		return index_.show_pointers();
	}

	vector<Unified> unify(const Term& t) const {
		vector<Unified> ret;
		if (!index_.size()) {
			return ret;
		}
		try {
			Timer timer;
			timer.start();
			map<uint, TermSubst> unif = unify_index_term(index_, t);
			add_timer_stats("unify_index_term", timer);

			for (auto& p : unif) {
				if (p.second.sub.ok()) {
					uint ind = p.first;
					const VarRepl& repl = stored_.at(ind).denorm;
					repl.apply(p.second.sub);
					ret.emplace_back(stored_.at(ind).data, std::move(p.second.sub));
				}
			}
		} catch (Error& err) {
			cout << "unify_index_term: " << endl;
			cout << index_.show() << endl << endl;
			cout << t.show() << endl << endl;
			throw err;
		}
		return ret;
	}

private:
	struct Storage {
		Storage(const Data& d, VarRepl&& s) : data(d), denorm(std::move(s)) { }
		Data data;
		VarRepl denorm;
	};
	Index index_;
	vector<Storage> stored_;
};

}}}}
