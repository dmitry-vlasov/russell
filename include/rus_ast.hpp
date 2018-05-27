#pragma once

#include "rus_expr.hpp"
#include "rus_sys.hpp"

namespace mdl { namespace rus {

struct Rule;
struct Proof;
struct Step;
struct Theory;
struct Import;
struct Source;

struct Comment : public Tokenable, public Writable  {
	Comment(bool ml = false, const string& txt = string(), const Token& t = Token()) : Tokenable(t), text(txt), multiline(ml) { }
	string text;
	bool multiline;
	void write(ostream& os, const Indent& i = Indent()) const override;
};

struct Const : public Owner<Const>, public Writable {
	Const(uint s, uint a, uint l, const Token& t = Token()) :
		Owner(s, t), symb(s), ascii(a), latex(l) { }
	Const(const Const& c) :
		Owner(c.id(), c.token), symb(c.symb), ascii(c.ascii), latex(c.latex) { }
	uint  symb;
	uint  ascii;
	uint  latex;
	void write(ostream& os, const Indent& i = Indent()) const override;
};

struct Vars : public Tokenable, public Writable {
	Vars(const vector<Symbol>& vars = vector<Symbol>(), const Token& t = Token()) : Tokenable(t), v(vars) { }
	Vars(const Vars& vars) : Tokenable(vars), v(vars.v) { }
	vector<Symbol> v;
	bool isDeclared(Symbol w) const {
		return std::find(v.begin(), v.end(), w) != v.end();
	}
	void write(ostream& os, const Indent& = Indent()) const override;
};

struct Disj : public Tokenable, public Writable {
	Disj(const vector<set<uint>>& disj = vector<set<uint>>(), const Token& t = Token()) :
		Tokenable(t), d(disj) { }
	Disj(const Disj& disj) : Tokenable(disj), d(disj.d), dmap(disj.dmap) { }
	vector<set<uint>> d;

	void init_dmap();
	void init_d();

	void write(ostream& os, const Indent& = Indent()) const override;
	void check(const Substitution&, const Theorem* t) const;
	void check(const Substitution&, Theorem* t) const;
	void pairs_are_disjointed(const set<uint>&, const set<uint>&) const;
	void make_pairs_disjointed(const set<uint>&, const set<uint>&);

private:
	map<uint, set<uint>> dmap;
};

void parse_expr(Expr& ex);

struct Type : public Owner<Type>, public Writable {
	typedef map<const Type*, unique_ptr<Rule>> Supers;
	Type(Id id, const vector<Id>& sup = vector<Id>(), const Token& t = Token());
	vector<User<Type>> sup;
	Supers supers;
	Rules  rules;
	void write(ostream& os, const Indent& i = Indent()) const override;
};

inline bool operator < (const Type& t1, const Type& t2) {
	for (const auto& t : t1.sup) if (t.get() == &t2) return true;
	return false;
}

struct Rule : public Owner<Rule>, public Writable {
	Rule(Id id, const Vars& v = Vars(), const Expr& e = Expr(), const Token& t = Token());
	Vars vars;
	Expr term;
	Type* type() { return term.type.get(); }
	const Type* type() const { return term.type.get(); }
	uint arity() const { return term.tree()->arity(); }
	void write(ostream& os, const Indent& i = Indent()) const override;
};

Rule* find_super(const Type* type, const Type* super);

inline Type* Tree::type() { return kind() == VAR ? var()->type() : rule()->term.type.get(); }
inline const Type* Tree::type() const { return kind() == VAR ? var()->type() : rule()->term.type.get(); }

struct Hyp : public Tokenable, public Writable {
	Hyp(uint i, const Expr& e = Expr(), const Token& t = Token()) :
		Tokenable(t), ind(i), expr(e) { }
	uint ind;
	Expr expr;
	void write(ostream& os, const Indent& i = Indent()) const override;
};

struct Prop : public Tokenable, public Writable {
	Prop(uint i, const Expr& e = Expr(), const Token& t = Token()) :
		Tokenable(t), ind(i), expr(e) { }
	uint ind;
	Expr expr;
	void write(ostream& os, const Indent& i = Indent()) const override;
};

struct Assertion : public Owner<Assertion> {
	enum Kind { AXM, THM, DEF };
	Assertion(Id i, const Token& t = Token()) : Owner(i.id, t) { }
	uint arity() const { return hyps.size(); }
	virtual Kind kind() const = 0;
	string kindStr() const {
		switch (kind()) {
		case AXM : return "axiom";
		case THM : return "theorem";
		case DEF : return "definition";
		default  : return "<none>";
		}
	}

	Vars vars;
	Disj disj;
	vector<unique_ptr<Hyp>>  hyps;
	vector<unique_ptr<Prop>> props;
	void write(ostream& os, const Indent& i = Indent()) const;
};

struct Axiom : public Assertion, public Writable {
	Axiom(Id id, const Token& t = Token()) : Assertion(id, t) { }
	Kind kind() const { return AXM; }
	void write(ostream& os, const Indent& i = Indent()) const override;
};

struct Def : public Assertion, public Writable {
	Def(Id id, const Token& t = Token()) : Assertion(id, t) { }
	Kind kind() const { return DEF; }
	Expr dfm;
	Expr dfs;
	Expr prop;
	void write(ostream& os, const Indent& i = Indent()) const override;
};

struct Theorem : public Assertion, public Writable {
	Theorem(Id id, const Token& t = Token()) : Assertion(id, t) { }
	Kind kind() const { return THM; }
	vector<User<Proof>> proofs;
	void write(ostream& os, const Indent& i = Indent()) const override;
};

struct Ref : public Tokenable, public Writable {
	enum Kind { HYP, PROP, STEP };
	Kind kind() const { return static_cast<Kind>(val.index()); }
	Ref(Hyp* h, const Token& t = Token())  : Tokenable(t), val(h)  { }
	Ref(Prop* p, const Token& t = Token()) : Tokenable(t), val(p)  { }
	Ref(Step* s, const Token& t = Token()) : Tokenable(t), val(s)  { }
	Expr& expr();
	const Expr& expr() const;
	Hyp* hyp() const { return std::get<Hyp*>(val); }
	Prop* prop() const { return std::get<Prop*>(val); }
	Step* step() const { return std::get<Step*>(val); }

	typedef variant<Hyp*, Prop*, Step*> Value;
	Value val;
	void write(ostream& os, const Indent& i = Indent()) const override;
};

struct Step : public Tokenable, public Writable {
	enum Kind { ASS, CLAIM };
	typedef variant<User<Assertion>, unique_ptr<Proof>> Value;

	Step(uint i, Step::Kind k, Id id, Proof* p, const Token& t = Token()) :
		Tokenable(t), ind_(i), proof_(p) {
		if (k == ASS) { val_ = std::move(User<Assertion>(id)); }
	}
	uint ass_id() const { return std::get<User<Assertion>>(val_).id(); }
	Assertion* ass() { return std::get<User<Assertion>>(val_).get(); }
	Proof* claim() { return std::get<unique_ptr<Proof>>(val_).get(); }
	const Assertion* ass() const { return std::get<User<Assertion>>(val_).get(); }
	const Proof* claim() const { return std::get<unique_ptr<Proof>>(val_).get(); }
	Proof* proof() { return proof_; }
	const Proof* proof() const { return proof_; }
	Kind kind() const { return static_cast<Kind>(val_.index()); }
	uint ind() const { return ind_; }
	void set_ind(uint ind) { ind_ = ind; }
	void verify() const;
	void write(ostream& os, const Indent& i = Indent()) const override;

	Expr expr;
	vector<unique_ptr<Ref>> refs;

private:
	uint   ind_;
	Value  val_;
	Proof* proof_;
};

inline Expr& Ref::expr() {
	switch (kind()) {
	case HYP : return hyp()->expr;
	case PROP: return prop()->expr;
	case STEP: return step()->expr;
	default  : assert(false && "impossible");
	}
	return step()->expr;
}

inline const Expr& Ref::expr() const {
	switch (kind()) {
	case HYP : return hyp()->expr;
	case PROP: return prop()->expr;
	case STEP: return step()->expr;
	default  : assert(false && "impossible");
	}
	return step()->expr;
}

struct Qed : public Tokenable, public Writable {
	Qed(Prop* p = nullptr, Step* s = nullptr, const Token& t = Token()) :
		Tokenable(t), prop(p), step(s) { }
	void verify() const;
	Prop* prop;
	Step* step;
	void write(ostream& os, const Indent& i = Indent()) const override;
};

struct Proof : public Owner<Proof>, public Writable {

	enum Kind { VARS, STEP, QED };
	typedef variant<unique_ptr<Vars>, unique_ptr<Step>, unique_ptr<Qed>> Elem;

	static Kind  kind(const Elem& e) { return static_cast<Kind>(e.index()); }
	static Vars* vars(const Elem& e) { return std::get<unique_ptr<Vars>>(e).get(); }
	static Step* step(const Elem& e) { return std::get<unique_ptr<Step>>(e).get(); }
	static Qed*  qed(const Elem& e) { return std::get<unique_ptr<Qed>>(e).get(); }

	Proof(Id thm, Id id = Id(), const Token& t = Token());

	Theorem* theorem() { return dynamic_cast<Theorem*>(thm.get()); }
	const Theorem* theorem() const { return dynamic_cast<const Theorem*>(thm.get()); }
	void verify() const;
	bool check() const;
	vector<Qed*> qeds() const;
	void write(ostream& os, const Indent& i = Indent()) const override;

	Vars            allvars;
	vector<Elem>    elems;
	User<Assertion> thm;
	Proof*          par;
	bool            inner;

};

struct Import : public Tokenable, public Writable {
	Import(uint src, const Token& t = Token()) : Tokenable(t), source(src) { }
	User<Source> source;
	void write(ostream& os, const Indent& i = Indent()) const override;
};

struct Theory : public Tokenable, public Writable {
	enum Kind { CONST, TYPE, RULE, AXIOM, DEF, THEOREM, PROOF, THEORY, IMPORT, COMMENT };
	typedef variant<
		unique_ptr<Const>,
		unique_ptr<Type>,
		unique_ptr<Rule>,
		unique_ptr<Axiom>,
		unique_ptr<Def>,
		unique_ptr<Theorem>,
		unique_ptr<Proof>,
		unique_ptr<Theory>,
		unique_ptr<Import>,
		unique_ptr<Comment>
	> Node;

	Theory(uint n = -1, Theory* p = nullptr, const Token& t = Token()) :
		Tokenable(t), id(n), nodes(), parent(p) { }
	void verify() const;
	void write(ostream& os, const Indent& i = Indent()) const override;
	static Kind kind(const Node& n) { return static_cast<Kind>(n.index()); }
	static Const* const_(const Node& n) { return std::get<unique_ptr<Const>>(n).get(); }
	static Type* type(const Node& n) { return std::get<unique_ptr<Type>>(n).get(); }
	static Rule* rule(const Node& n) { return std::get<unique_ptr<Rule>>(n).get(); }
	static Axiom* axiom(const Node& n) { return std::get<unique_ptr<Axiom>>(n).get(); }
	static Def* def(const Node& n) { return std::get<unique_ptr<Def>>(n).get(); }
	static Theorem* theorem(const Node& n) { return std::get<unique_ptr<Theorem>>(n).get(); }
	static Proof* proof(const Node& n) { return std::get<unique_ptr<Proof>>(n).get(); }
	static Theory* theory(const Node& n) { return std::get<unique_ptr<Theory>>(n).get(); }
	static Import* import(const Node& n) { return std::get<unique_ptr<Import>>(n).get(); }
	static Comment* comment(const Node& n) { return std::get<unique_ptr<Comment>>(n).get(); }

	uint         id;
	vector<Node> nodes;
	Theory*      parent;
};

struct Source : public mdl::Source<Source, Sys> {
	Source(uint l) : mdl::Source<Source, Sys>(l) { }
	Tokenable* find(const Token& t);
	void write(ostream& os, const Indent& i = Indent()) const override;

	Theory theory;
};

string xml_outline(const Source&, uint);
string xml_structure(uint bits);
template<class T> string xml_struct(uint bits);

size_t memvol(const Source&);

void add_to_index(Assertion*);
void add_to_index(Proof*);
Proof* prove(Assertion*);
bool test_with_oracle();

}} // mdl::rus
