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
		std::map<RuleVar, Node>::iterator parent;
		vector<uint> vals;
		std::map<RuleVar, Node> map;

		set<std::map<RuleVar, Node>::const_iterator, NodeIterLess> ends; // All ends of terms, which start at current node
		set<std::map<RuleVar, Node>::const_iterator, NodeIterLess> vars; // All variables among nodes
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
	string showTypes() const;
	string showPointers() const;

	static Unpacked unpack(const Node&);
	static Unpacked unpack(Iter);
	static string show(const Node&);
	static string show(Iter);
	static string showTypes(const Node&);
	static string showTypes(Iter);
	static string showPointers(const Node&);

	uint totalNodes() const;
	bool empty() const { return root_.map.empty(); }
	void verify(bool show = false) const;

	uint size() const { return size_; }
	const Node& root() const {
		if (!endsInitialized) {
			const_cast<Index*>(this)->initEnds();
		}
		return root_;
	}
	map<uint, TermSubst> unify(const Term& t) const;
	const vector<uint>* find(const Term& t) const;

private:
	void initEnds();
	uint size_ = 0;
	Node root_;
	bool endsInitialized = false;
	vector<Term> terms;
};

struct Index::Iter {
	Iter() : node_(nullptr) { }
	Iter(const Node& n) : iter_(n.map.size() ? n.map.begin() : ConstIterator()), node_(&n) { }
	Iter(const Node* n, ConstIterator i = ConstIterator()) : iter_(i), node_(n) { }
	Iter(const Iter&) = default;
	Iter& operator = (const Iter&) = default;
	bool operator == (const Iter& i) const {
		return iter_ == i.iter_;
	}
	bool operator != (const Iter& i) const {
		return !operator ==(i);
	}
	Iter side() const {
		if (!isValid() || isSideEnd()) {
			return Iter();
		} else {
			auto i = iter_;
			return Iter(node_, ++i);
		}
	}
	Iter next() const {
		if (!isValid() || isNextEnd()) {
			return Iter();
		} else {
			return Iter(&iter_->second, iter_->second.map.begin());
		}
	}
	Iter prev() const {
		return Iter(nullptr, iter_->second.parent);
	}
	Iter reset() const {
		return isValid() ? Iter(node_, node_->map.begin()) : Iter();
	}
	bool isNextEnd() const {
		return !isValid() || iter_->second.map.size() == 0;
	}
	bool isSideEnd() const {
		if (!isValid()) {
			return true;
		} else {
			auto i = iter_; ++i;
			return i == node_->map.end();
		}
	}
	bool isValid() const {
		return iter_ != ConstIterator();
	}
	ConstIterator iter() const {
		if (!isValid()) {
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
		ret.reserve(node_->vars.size());
		for (auto var : node_->vars) {
			ret.emplace_back(node_, var);
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
	ConstIterator iter_;
	const Node* node_;
};

struct Normalizer {
	Normalizer(const Term& t) : normalized(t) {
		for (auto& n : normalized.nodes) {
			normalize(n.ruleVar);
		}
	}

	VarRepl norm;
	Term normalized;

private:
	void normalize(RuleVar& rv) {
		if (rv.isVar() && rv.var.rep) {
			LightSymbol v = rv.var;
			LightSymbol norm_v = norm.direct().replace(v);
			if (norm_v.is_undef()) {
				uint c = 0;
				auto ti = types.find(rv.var.type);
				if (ti != types.end()) {
					c = ti->second + 1;
				}
				types[rv.var.type] = c;
				norm_v.rep = true;
				norm_v.type = v.type;
				norm_v.lit = Lex::toInt(Lex::toStr(rv.var.type->id()) + "_" + to_string(c));
				norm.compose(VarPair(v, norm_v));
				rv.var = norm_v;
			} else {
				rv.var = norm_v;
			}
		}
	}
	hmap<const Type*, uint> types;
};

map<uint, TermSubst> unify_index_term(const Index& ind, const Term& term);
map<uint, TermVarRepl> varify_index_term(const Index& ind, const Term& term);

template<class Data>
struct IndexMap {
	struct Unified {
		Unified(const Data& d, Subst&& s) : data(&d), sub(std::move(s)) { }
		Unified(const Unified&) = default;
		Unified(Unified&&) = default;
		const Data* data;
		Subst sub;
	};
	struct Replaced {
		Replaced(const Data& d, VarRepl&& r) : data(&d), repl(std::move(r)) { }
		Replaced(const Replaced&) = default;
		Replaced(Replaced&&) = default;
		const Data* data;
		VarRepl repl;
	};
	void add(const Term& t, const Data& d) {
		Normalizer n(t);
		index_.add(n.normalized, stored_.size());
		stored_.emplace_back(d, std::move(n.norm));
	}
	void emplace(const Term& t, Data&& d) {
		Normalizer n(t);
		index_.add(n.normalized, stored_.size());
		stored_.emplace_back(std::move(d), std::move(n.norm));
	}
	string show() const {
		Index::Unpacked terms = index_.unpack();
		if (!terms.size()) {
			return "\n";
		} else {
			string ret;
			for (auto&  p : terms) {
				for (uint i : p.second) {
					const VarRepl& norm = stored_.at(i).norm;
					norm.inverse().apply(p.first);
					ret += "[" + p.first.show() + "]" + " -> " + to_string(i) + "\n";
				}
			}
			return ret;
		}
	}
	string showPointers() const {
		return index_.showPointers();
	}
	string showTypes() const {
		return index_.showTypes();
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

			timer.start();
			for (auto& p : unif) {
				if (p.second.sub.ok()) {
					uint ind = p.first;
					const VarRepl& repl = stored_.at(ind).norm;
					repl.inverse().apply(p.second.sub);
					ret.emplace_back(stored_.at(ind).data, std::move(p.second.sub));
				}
			}
			add_timer_stats("Index::unify: form result", timer);
		} catch (Error& err) {
			cout << "unify_index_term: " << endl;
			cout << index_.show() << endl << endl;
			cout << t.show() << endl << endl;
			throw err;
		}
		return ret;
	}
	vector<Replaced> find(const Term& t) const {
		const Normalizer n(t);
		vector<Replaced> ret;
		const vector<uint>* inds = index_.find(n.normalized);
		if (inds) {
			for (uint ind : *inds) {
				const VarRepl& norm = stored_.at(ind).norm;
				VarRepl repl = norm.inversed().compose(n.norm);
				ret.emplace_back(stored_.at(ind).data, std::move(repl));
			}
		}
		return ret;
	}
	vector<const Data*> findExact(const Term& t) const {
		const Normalizer n(t);
		vector<const Data*> ret;
		const vector<uint>* inds = index_.find(n.normalized);
		if (inds) {
			for (uint ind : *inds) {
				const VarRepl& norm = stored_.at(ind).norm;
				VarRepl repl = norm.inversed().compose(n.norm);
				if (repl.size() == 0) {
					ret.push_back(&stored_.at(ind).data);
				}
			}
		}
		return ret;
	}
	bool contains(const Term& t) const {
		return findExact(t).size();
	}
	uint size() const {
		return index_.size();
	}
	void init() {
		index_.root();
	}

private:
	struct Storage {
		Storage(const Data& d, VarRepl&& s) : data(d), norm(std::move(s)) { }
		Storage(Data&& d, VarRepl&& s) : data(std::move(d)), norm(std::move(s)) { }
		Data data;
		VarRepl norm;
	};
	Index index_;
	vector<Storage> stored_;
};

}}}}
