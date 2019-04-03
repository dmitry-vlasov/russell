#pragma once

#include "../rus_prover_expr.hpp"

namespace mdl { namespace rus { namespace prover { namespace trie_index {

struct RuleVar {
	const Rule* rule = nullptr;
	LightSymbol var;
	bool operator == (const RuleVar& rv) const { return rule == rv.rule && var == rv.var; }
	bool operator != (const RuleVar& rv) const { return !operator == (rv); }
	bool operator < (const RuleVar& rv) const {
		if (isVar()) {
			return rv.isRule() ? true : var < rv.var;
		} else {
			return rv.isRule() ? rule < rv.rule : false;
		}
	}
	string show() const { return rule ? Lex::toStr(rule->id()) : prover::show(var); }
	bool isVar() const  { return var.is_def(); }
	bool isRule() const { return rule; }
	const Type* type() const { return rule ? rule->type() : var.type; }
	Var _var() const { return Var(var.lit, var.type); }
};

struct FlatTerm {
	enum Kind { RULE, VAR };
	struct Node {
		Node() { }
		Node(const RuleVar& rv) : ruleVar(rv) { }
		Node(const Node& n) : ruleVar(n.ruleVar) { }
		Node(Node&&) = delete;
		bool operator == (const Node& n) const { return ruleVar == n.ruleVar; }
		bool operator != (const Node& n) const { return ruleVar != n.ruleVar; }
		Node& operator = (const Node& n) { ruleVar = n.ruleVar; return *this;}
		Node& operator = (Node&&) = delete;
		RuleVar ruleVar;
		vector<Node>::const_iterator end;
	};
	typedef vector<Node>::iterator Iterator;
	typedef vector<Node>::const_iterator ConstIterator;

	struct TermIter {
		TermIter() : valid_(false) { }
		TermIter(const FlatTerm& ft) :
			valid_(true),
			beg_(ft.nodes.begin()),
			iter_(ft.nodes.begin()),
			end_(ft.nodes.begin() + ft.len() - 1) { }
		TermIter(ConstIterator b, ConstIterator e, bool v = true) :
			valid_(v), beg_(b), iter_(b), end_(e) { }
		TermIter(const TermIter&) = default;
		TermIter& operator = (const TermIter&) = default;
		bool operator == (const TermIter& i) const {
			return iter_ == i.iter_;
		}
		bool operator != (const TermIter& i) const {
			return iter_ != i.iter_;
		}
		TermIter side() const {
			return TermIter(beg_, iter_, end_, false);
		}
		TermIter next() const {
			if (!valid_ || isNextEnd()) {
				return TermIter(beg_, iter_, end_, false);
			} else {
				return TermIter(beg_, iter_ + 1, end_, iter_ != end_);
			}
		}
		TermIter prev() const {
			if (!valid_ || isPrevEnd()) {
				return TermIter();
			} else {
				return TermIter(beg_, iter_ - 1, end_, iter_ != beg_);
			}
		}
		TermIter fastForward() const {
			return TermIter(beg_, valid_ ? iter_->end : iter_, end_, valid_);
		}
		TermIter reset() const {
			return TermIter(beg_, end_, valid_);
		}
		FlatTerm subTerm() const;
		FlatTerm term() const;
		vector<pair<FlatTerm, TermIter>> subTerms() const {
			vector<pair<FlatTerm, TermIter>> ret;
			ret.reserve(1);
			ret.emplace_back(subTerm(), fastForward());
			return ret;
		}
		vector<TermIter> ends() const {
			vector<TermIter> ret;
			ret.reserve(1);
			ret.push_back(fastForward());
			return ret;
		}
		bool isEnd(const TermIter& i) const {
			return iter_->end == i.iter_;
		}
		bool isVar() const {
			return iter_->ruleVar.isVar() && iter_->ruleVar.var.rep;
		}
		LightSymbol var() const {
			return iter_->ruleVar.var;
		}
		RuleVar ruleVar() const {
			return iter_->ruleVar;
		}
		bool isNextEnd() const { return iter_ == end_; }
		bool isPrevEnd() const { return iter_ == beg_; }
		bool isSideEnd() const { return true; }
		bool isValid() const { return valid_; }
		ConstIterator iter() const {
			if (!valid_) {
				cout << "NOT VALID FlatTerm::TermIter !!!" << endl;
			}
			assert(valid_ && "TermIter::iter()");
			return iter_;
		}

		vector<ConstIterator> childrenIters() const {
			vector<ConstIterator> ret;
			if (valid_ && iter_->ruleVar.isRule()) {
				ConstIterator x = iter_;
				for (uint i = 0; i < iter_->ruleVar.rule->arity(); ++i) {
					ret.push_back(x);
					x = x->end + 1;
				}
			} else {
				throw Error("node has no children");
			}
			return ret;
		}
		string show(bool full = false) const {
			string ret;
			if (full) {
				ret += "beg: " + ((beg_ == ConstIterator()) ? "<>" : beg_->ruleVar.show()) + "\n";
				ret += "iter: " + ((iter_ == ConstIterator()) ? "<>" : iter_->ruleVar.show()) + "\n";
				ret += "end: " + ((end_ == ConstIterator()) ? "<>" : end_->ruleVar.show()) + "\n";
				ret += "len: " + to_string((end_ - beg_) + 1) + "\n";
			} else {
				ret += iter_->ruleVar.show() + " ";
			}
			return ret;
		}
		string showBranch() const {
			vector<TermIter> branch;
			TermIter i = *this;
			while (i.isValid()) {
				branch.push_back(i);
				i = i.prev();
			}
			std::reverse(branch.begin(), branch.end());
			string ret;
			for (auto it : branch) {
				ret += it.show();
			}
			return ret;
		}

	private:
		TermIter(ConstIterator b, ConstIterator i, ConstIterator e, bool v = true) :
			valid_(v), beg_(b), iter_(i), end_(e) { }
		bool valid_;
		ConstIterator beg_;
		ConstIterator iter_;
		ConstIterator end_;
	};

	FlatTerm(uint s = 0) : nodes(s) { }
	FlatTerm(const FlatTerm&);
	FlatTerm(FlatTerm&&) = default;
	FlatTerm(LightSymbol s);
	FlatTerm(ConstIterator i);
	FlatTerm(const Rule* r, const vector<FlatTerm>& ch);

	bool operator == (const FlatTerm& t) const { return nodes == t.nodes; }
	bool operator != (const FlatTerm& t) const { return nodes != t.nodes; }

	FlatTerm& operator = (const FlatTerm&);
	FlatTerm& operator = (FlatTerm&&) = default;

	Kind kind() const {
		return (nodes.size() == 1 && nodes[0].ruleVar.isVar()) ? VAR : RULE;
	}
	LightSymbol var() const { assert(kind() == VAR); return nodes[0].ruleVar.var; }
	const Rule* rule() const { assert(kind() == RULE); return nodes[0].ruleVar.rule; }
	bool empty() const { return !nodes.size(); }
	uint len() const { return nodes.size(); }
	vector<FlatTerm> children() const;
	vector<ConstIterator> childrenIters() const;
	FlatTerm subTerm(ConstIterator beg) const;
	void verify() const;

	vector<Node> nodes;
	string show(bool simple = false) const;
	string show_pointers() const;
};

FlatTerm convert2flatterm(const LightTree&);
LightTree convert2lighttree(const FlatTerm&);

FlatTerm tree2flatterm(const Tree&);
unique_ptr<Tree> flatterm2tree(const FlatTerm&);

void copyFlatSubTerm(FlatTerm* t, const uint pos, FlatTerm::ConstIterator b);
FlatTerm term(FlatTerm::ConstIterator b);

extern bool debug_flatterm;

}}}}
