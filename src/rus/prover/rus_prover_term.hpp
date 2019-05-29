#pragma once

#include "rus_ast.hpp"

namespace mdl { namespace rus { namespace prover {

enum class ReplMode {
	KEEP_REPL,
	DENY_REPL
};

struct LightSymbol {
	enum {
		MATH_INDEX = 0,
		ASSERTION_INDEX = 1,
		INTERNAL_MIN_INDEX = 2
	};
	LightSymbol() : lit(undef_value()), rep(false), ind(-1), type(nullptr) { }
	explicit LightSymbol(uint l, bool r = true) : lit(l), rep(r), ind(-1), type(nullptr) { }
	LightSymbol(uint l, const Type* t, ReplMode mode = ReplMode::KEEP_REPL, uint i = MATH_INDEX) :
		lit(i == MATH_INDEX ? l :
			(i == ASSERTION_INDEX ? Lex::toInt(Lex::toStr(l) + "!") :
				Lex::toInt(Lex::toStr(l) + "_" + to_string(i - LightSymbol::INTERNAL_MIN_INDEX))
			)
		),
		rep(t),
		ind(i),
		type(t) {
		if (mode == ReplMode::DENY_REPL) {
			rep = false;
		}
	}
	LightSymbol(const rus::Symbol& s, ReplMode mode, uint i) :
		lit(i == MATH_INDEX ? s.lit() :
			(i == ASSERTION_INDEX ? Lex::toInt(Lex::toStr(s.lit()) + "!") :
				Lex::toInt(Lex::toStr(s.lit()) + "_" + to_string(i - LightSymbol::INTERNAL_MIN_INDEX))
			)
		),
		rep(s.kind() == Symbol::VAR),
		ind(i),
		type(s.kind() == Symbol::VAR ? s.type() : nullptr) {
		if (mode == ReplMode::DENY_REPL) {
			rep = false;
		}
	}
	LightSymbol(const LightSymbol& s) = default;

	bool is_undef() const { return lit == undef_value(); }
	bool is_def() const { return lit != undef_value(); }
	uint literal() const { return lit; }
	static uint undef_value() { static uint val = uint(-1) >> 1; return val; }

	bool operator == (const LightSymbol& s) const { return lit == s.lit; }
	bool operator != (const LightSymbol& s) const { return !operator ==(s); }
	bool operator == (uint s) const { return lit == s; }
	bool operator != (uint s) const { return !operator ==(s); }
	bool operator < (const LightSymbol& s) const {
		if (lit < s.lit) return true;
		else if (lit > s.lit) return false;
		else return ind < s.ind;
	}

	LightSymbol& operator = (const LightSymbol& s) = default;
	LightSymbol& operator = (const Symbol& s) {
		lit = s.lit();
		type = s.type();
		ind = 0;
		rep = (s.kind() == Symbol::VAR);
		return *this;
	}

	string show(bool full = false) const {
		return (is_undef() ? "<UNDEF>" : Lex::toStr(lit)) + (full && rep ? "*" : "");
	}

	struct Hash {
		typedef size_t result_type;
		typedef Symbol argument_type;
		size_t operator() (const LightSymbol& s) const {
			return hash(s.lit);
		}
	private:
		static std::hash<uint> hash;
	};

	uint lit:31;
	bool rep:1;
	uint ind;
	const Type* type;
};

string show(const set<uint>&);
string show(const vector<uint>&);
string show(const vector<bool>& v);
string show(const vector<LightSymbol>& v);

inline ostream& operator << (ostream& os, const LightSymbol& s) {
	os << s.show(); return os;
}

struct RuleVar {
	RuleVar() = default;
	RuleVar(const Rule* r) : rule(r) { }
	RuleVar(LightSymbol v) : var(v) { }
	RuleVar(const RuleVar&) = default;

	bool operator == (const RuleVar& rv) const { return rule == rv.rule && var == rv.var; }
	bool operator != (const RuleVar& rv) const { return !operator == (rv); }
	bool operator < (const RuleVar& rv) const {
		if (isVar()) {
			return rv.isRule() ? true : var < rv.var;
		} else {
			return rv.isRule() ? rule < rv.rule : false;
		}
	}
	string show() const { return rule ? Lex::toStr(rule->id()) : var.show(true); }
	bool isVar() const  { return var.is_def(); }
	bool isRule() const { return rule; }
	const Type* type() const { return rule ? rule->type() : var.type; }
	Var _var() const { return Var(var.lit, var.type); }

	const Rule* rule = nullptr;
	LightSymbol var;
};

inline ostream& operator << (ostream& os, const RuleVar& rv) {
	os << rv.show(); return os;
}

struct Term {
	struct Iter;
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

	Term(uint s = 0) : nodes(s) { }
	Term(const Term&);
	Term(Term&&) = default;
	Term(LightSymbol s);
	Term(ConstIterator i);
	Term(const Rule* r, const vector<Term>& ch);

	bool operator == (const Term& t) const { return nodes == t.nodes; }
	bool operator != (const Term& t) const { return nodes != t.nodes; }

	Term& operator = (const Term&);
	Term& operator = (Term&&) = default;

	Kind kind() const {
		return (nodes.size() == 1 && nodes[0].ruleVar.isVar()) ? VAR : RULE;
	}
	LightSymbol var() const { assert(kind() == VAR); return nodes[0].ruleVar.var; }
	const Rule* rule() const { assert(kind() == RULE); return nodes[0].ruleVar.rule; }
	bool empty() const { return !nodes.size(); }
	vector<Term> children() const;
	vector<ConstIterator> childrenIters() const;
	Term subTerm(ConstIterator beg) const;
	const Type* type() const { return nodes.front().ruleVar.type(); }
	void verify() const;
	uint linearLen() const; // Length of a corresponding linear expression
	uint len() const { return nodes.size(); }
	set<uint> vars() const;

	vector<Node> nodes;
	string show(bool simple = false) const; // simple = false for corresponding linear expression
	string show_pointers() const;
};

inline ostream& operator << (ostream& os, const Term& t) {
	os << t.show(); return os;
}

struct Term::Iter {
	Iter() : valid_(false) { }
	Iter(const Term& ft) :
		valid_(true),
		beg_(ft.nodes.begin()),
		iter_(ft.nodes.begin()),
		end_(ft.nodes.begin() + ft.nodes.size() - 1) { }
	Iter(ConstIterator b, ConstIterator e, bool v = true) :
		valid_(v), beg_(b), iter_(b), end_(e) { }
	Iter(const Iter&) = default;
	Iter& operator = (const Iter&) = default;
	bool operator == (const Iter& i) const {
		return iter_ == i.iter_;
	}
	bool operator != (const Iter& i) const {
		return iter_ != i.iter_;
	}
	Iter side() const {
		return Iter(beg_, iter_, end_, false);
	}
	Iter hint(const Rule* r) const {
		if (iter_->ruleVar.rule == r) {
			return *this;
		} else {
			return Iter();
		}
	}
	void setHint(const Rule* r) {
		if (iter_->ruleVar.isRule() && iter_->ruleVar.rule != r) {
			valid_ = false;
		}
	}
	Iter next() const {
		if (!valid_ || isNextEnd()) {
			return Iter(beg_, iter_, end_, false);
		} else {
			return Iter(beg_, iter_ + 1, end_, iter_ != end_);
		}
	}
	Iter prev() const {
		if (!valid_ || isPrevEnd()) {
			return Iter();
		} else {
			return Iter(beg_, iter_ - 1, end_, iter_ != beg_);
		}
	}
	//Iter fastForward() const {
	//	return end();
	//}
	Iter reset() const {
		return Iter(beg_, end_, valid_);
	}
	Term subTerm() const;
	Term term() const;
	vector<pair<Term, Iter>> subTerms() const {
		vector<pair<Term, Iter>> ret;
		ret.reserve(1);
		ret.emplace_back(subTerm(), end());
		return ret;
	}
	vector<Iter> ends() const {
		vector<Iter> ret;
		ret.reserve(1);
		ret.push_back(end());
		return ret;
	}
	Iter end() const {
		return Iter(beg_, valid_ ? iter_->end : iter_, end_, valid_);
	}
	bool isEnd(const Iter& i) const {
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
	const Node& node() const {
		return *iter_;
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
		vector<Iter> branch;
		Iter i = *this;
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
	string showTree() const {
		return term().show();
	}

private:
	Iter(ConstIterator b, ConstIterator i, ConstIterator e, bool v = true) :
		valid_(v), beg_(b), iter_(i), end_(e) { }
	bool valid_;
	ConstIterator beg_;
	ConstIterator iter_;
	ConstIterator end_;
};

Term Tree2Term(const Tree&, ReplMode m = ReplMode::KEEP_REPL, uint i = 0);
unique_ptr<Tree> Term2Tree(const Term&);
rus::Expr Term2Expr(const Term&);

void copySubTerm(Term* t, const uint pos, Term::ConstIterator b);
Term term(Term::ConstIterator b);

}}}
