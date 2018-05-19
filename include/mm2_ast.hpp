#pragma once

#include "mm2_expr.hpp"

namespace mdl { namespace mm2 {

typedef mdl::Token<Source> Token;
typedef mdl::Tokenable<Source> Tokenable;
typedef mdl::Id<Source> Id;

class Source;
class Assertion;

struct Comment : public Writable {
	string text;
	Comment(const string& t) : text(t) { }
	void write(ostream& os, const Indent& i = Indent()) const override {
		os << i << "$( " << text << " $)\n";
	}
};

struct Import : public Writable {
	User<Source> source;
	Import(uint id) : source(id) { }
	void write(ostream& os, const Indent& i = Indent()) const override {
		os << i << "$[ " << Lex::toStr(source.id()) << ".mm $]\n";
	}
};

struct Const : public Writable {
	uint symb;
	Const(uint s) : symb(s) { }
	void write(ostream& os, const Indent& i = Indent()) const override {
		os << i << "$c " << Lex::toStr(symb) << " $.\n";
	}
};

struct Vars : public Writable {
	vector<uint> vars;
	void write(ostream& os, const Indent& i) const override {
		if (vars.size()) {
			os << i << "$v "; for (uint v : vars) os << Lex::toStr(v) << " "; os << " $.\n";
		}
	}
};

struct Disj : public Writable {
	vector<unique_ptr<vector<uint>>> vect;
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
	void write(ostream& os, const Indent& i = Indent()) const override {
		os << i; ref(os); os << " $f " << Lex::toStr(type()) << " " << Lex::toStr(var()) << " $.\n";
	}
	void ref(ostream& os) const override {
		os << (inner ? 'i' : 'f') << index << '_' << Lex::toStr(label) << ' ';
	}
};

struct Ref : public Writable {
	typedef User<Assertion> Ass;

	Ref(Hyp* h) : val(h) { }
	Ref(Var* v) : val(v) { }
	Ref(uint l) : val(Ass(l)) { }

	bool is_assertion() const { return val.index() == 2; }
	Hyp* hyp() { return std::get<Hyp*>(val); }
	Var* var() { return std::get<Var*>(val); }
	Assertion* ass() { return std::get<Ass>(val).get(); }
	const Hyp* hyp() const { return std::get<Hyp*>(val); }
	const Var* var() const { return std::get<Var*>(val); }
	const Assertion* ass() const { return std::get<Ass>(val).get(); }

	uint label() const {
		switch (val.index()) {
		case 0 : return var()->label;
		case 1 : return hyp()->label;
		case 2 : return std::get<Ass>(val).id();
		}
	}
	uint index() const {
		switch (val.index()) {
		case 0 : return var()->index;
		case 1 : return hyp()->index;
		default : assert(false && "must not be assertion"); return -1;
		}
	}

	void write(ostream& os, const Indent& i = Indent()) const override;

	variant<Var*, Hyp*, Ass> val;
};

struct Proof : public Writable {
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
	~Assertion() override { }

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
	switch (val.index()) {
	case 0 : var()->ref(os); break;
	case 1 : hyp()->ref(os); break;
	case 2 : ass()->ref(os); break;
	default : assert(false && "impossible");
	}
}

struct Source : public mdl::Source<Source, Sys>, public Writable {
	typedef variant<
		unique_ptr<Const>,
		unique_ptr<Import>,
		unique_ptr<Comment>,
		unique_ptr<Assertion>
	> Node;

	enum Kind { CONST, IMPORT, COMMENT, ASSERTION };
	static Kind kind(const Node& n) { return static_cast<Kind>(n.index()); }

	Source(uint l) : mdl::Source<Source, Sys>(l) { }

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


