#pragma once

#include "mm_expr.hpp"

namespace mdl { namespace mm {

typedef mdl::Token<Source> Token;
typedef mdl::Tokenable<Source> Tokenable;
typedef mdl::Id<Source> Id;

class Source;
class Assertion;

struct Comment : public Writable {
	string text;
	Comment(const string& t) : text(t) { }
	Comment(const Comment&) = delete;
	void write(ostream& os, const Indent& i = Indent()) const override {
		os << i << "$( " << text << " $)\n";
	}
};

struct Import : public Writable {
	User<Source> source;
	Import(uint id) : source(id) { }
	Import(const Import&) = delete;
	void write(ostream& os, const Indent& i = Indent()) const override {
		os << i << "$[ " << Lex::toStr(source.id()) << ".mm $]\n";
	}
};

struct Const : public Writable {
	uint symb;
	Const(uint s) : symb(s) { }
	Const(const Const&) = delete;
	void write(ostream& os, const Indent& i = Indent()) const override {
		os << i << "$c " << Lex::toStr(symb) << " $.\n";
	}
};

struct Vars : public Writable {
	vector<uint> vars;
	Vars() = default;
	Vars(const Vars&) = delete;
	void write(ostream& os, const Indent& i) const override {
		if (vars.size()) {
			os << i << "$v "; for (uint v : vars) os << Lex::toStr(v) << " "; os << " $.\n";
		}
	}
};

struct Disj : public Writable {
	vector<unique_ptr<set<uint>>> vect;
	Disj() = default;
	Disj(const Disj&) = delete;
	void write(ostream& os, const Indent& i = Indent()) const override {
		for (const auto& vars : vect) {
			os << i << "$d "; for (uint v : *vars.get()) os << Lex::toStr(v) << " "; os << " $.\n";
		}
	}
};

struct Hyp : public Writable, public Referable {
	uint index;
	uint label;
	Expr expr;
	Hyp(uint i, uint l) : index(i), label(l) { }
	Hyp(const Hyp&) = delete;
	void write(ostream& os, const Indent& i = Indent()) const override {
		os << i; ref(os); os << "$e " << expr << "$.\n";
	}
	void ref(ostream& os) const override {
		os << 'e' << index << '_' << Lex::toStr(label) << ' ';
	}
};

struct Var : public Writable, public Referable {
	bool inner;
	uint index;
	uint label;
	Expr expr;
	uint type() const { return expr[0].lit; }
	uint var() const { return expr[1].lit; }
	Var(bool i, uint ind, uint l, uint t, uint v) : inner(i), index(ind), label(l) {
		expr.reserve(2);
		expr.emplace_back(t, false);
		expr.emplace_back(v, true);
	}
	Var(const Var&) = delete;
	void write(ostream& os, const Indent& i = Indent()) const override {
		os << i; ref(os); os << " $f " << Lex::toStr(type()) << " " << Lex::toStr(var()) << " $.\n";
	}
	void ref(ostream& os) const override {
		os << (inner ? 'i' : 'f') << index << '_' << Lex::toStr(label) << ' ';
	}
};

struct Ref : public Writable {
	typedef User<Assertion> Ass;
	enum Kind { VAR, HYP, ASS };

	Ref(Hyp* h) : val(h) { }
	Ref(Var* v) : val(v) { }
	Ref(uint l) : val(Ass(l)) { }
	Ref(const Ref&) = default;

	Kind kind() const { return static_cast<Kind>(val.index()); }
	bool is_assertion() const { return kind() == ASS; }
	Hyp* hyp() const { return std::get<Hyp*>(val); }
	Var* var() const { return std::get<Var*>(val); }
	const Assertion* ass() const { return std::get<Ass>(val).get(); }

	uint label() const {
		switch (kind()) {
		case VAR : return var()->label;
		case HYP : return hyp()->label;
		case ASS : return std::get<Ass>(val).id();
		default : assert(false && "impossible"); return -1;
		}
	}
	uint index() const {
		switch (val.index()) {
		case VAR : return var()->index;
		case HYP : return hyp()->index;
		default : assert(false && "must not be assertion"); return -1;
		}
	}

	void write(ostream& os, const Indent& i = Indent()) const override;

	variant<Var*, Hyp*, Ass> val;
};

struct Proof : public Writable {
	Proof() : theorem(nullptr) { }
	Proof(const Proof&) = delete;
	vector<Ref> refs;
	Assertion*  theorem;
	void write(ostream& os, const Indent& i = Indent()) const override {
		if (refs.size()) {
			os << i;
			for (const auto& r : refs) os << r;
			os << "$.\n";
		}
	}
};

struct Assertion : public Owner<Assertion>, public Writable, public Referable {
	Assertion (uint label, const Token& t = Token()) : Owner(label, t) { }
	Assertion(const Assertion&) = delete;

	uint arity() const { return hyps.size() + outerVars.size(); }
	bool axiom() const { return !proof.refs.size(); }

	Vars vars;
	Disj disj;
	vector<unique_ptr<Var>> outerVars;
	vector<unique_ptr<Var>> innerVars;
	vector<unique_ptr<Hyp>> hyps;
	Expr  expr;
	Proof proof;

	void write(ostream& os, const Indent& ind = Indent()) const override {
		Indent incInd = ind + 1;
		os << ind << "${\n";
		vars.write(os, incInd);
		disj.write(os, incInd);
		for (const auto& o : outerVars) o.get()->write(os, incInd);
		for (const auto& i : innerVars) i.get()->write(os, incInd);
		for (const auto& h : hyps) h.get()->write(os, incInd);
		os << incInd; ref(os);
		os << (axiom() ? "$a " : "$p ") << expr << (axiom() ? "$." : "$=") << "\n";
		proof.write(os, incInd);
		os << ind << "$}\n";
	}
	void ref(ostream& os) const override {
		os << (axiom() ? 'a' : 'p') << '_' << Lex::toStr(id()) << ' ';
	}
};

inline void Ref::write(ostream& os, const Indent& i) const {
	switch (kind()) {
	case VAR : var()->ref(os); break;
	case HYP : hyp()->ref(os); break;
	case ASS : ass()->ref(os); break;
	default : assert(false && "impossible");
	}
}

struct Source : public mdl::Source<Source, Sys> {
	typedef variant<
		unique_ptr<Const>,
		unique_ptr<Import>,
		unique_ptr<Comment>,
		unique_ptr<Assertion>
	> Node;

	enum Kind { CONST, IMPORT, COMMENT, ASSERTION };
	static Kind kind(const Node& n) { return static_cast<Kind>(n.index()); }

	Source(uint l) : mdl::Source<Source, Sys>(l) { }
	Source(const Source&) = delete;

	vector<Node> contents;

	void write(ostream& os, const Indent& i = Indent()) const override {
		for (const Node& n : contents) {
			switch (n.index()) {
			case CONST:     std::get<unique_ptr<Const>>(n).get()->write(os, i);     break;
			case IMPORT:    std::get<unique_ptr<Import>>(n).get()->write(os, i);    break;
			case COMMENT:   std::get<unique_ptr<Comment>>(n).get()->write(os, i);   break;
			case ASSERTION: std::get<unique_ptr<Assertion>>(n).get()->write(os, i); break;
			}
			os << '\n';
		}
	}
};

typedef map<Symbol, Expr> Subst;
Expr apply(const Subst& sub, const Expr& expr);

}} // mdl::mm


