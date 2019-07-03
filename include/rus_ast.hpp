#pragma once

#include "dag.hpp"
#include "rus_expr.hpp"
#include "rus_sys.hpp"

namespace mdl { namespace rus {

struct Rule;
struct Proof;
struct Step;
struct Theory;
struct Import;
struct Source;

struct Comment : public Writable, public WithToken  {
	Comment(bool ml = false, const string& txt = string(), const Token& t = Token()) : WithToken(t), text(txt), multiline(ml) { }
	Comment(const Comment&) = delete;
	string text;
	bool multiline;
	void write(ostream& os, const Indent& i = Indent()) const override;
};

struct Constant : public Owner<Constant>, public Writable {
	Constant(uint s, uint a, uint l, const Token& t = Token()) :
		Owner(s, t), symb(s), ascii(a), latex(l) { }
	Constant(const Constant& c) = delete;
	uint  symb;
	uint  ascii;
	uint  latex;
	void write(ostream& os, const Indent& i = Indent()) const override;
};

struct Vars : public Writable, public WithToken {
	Vars(const vector<Var>& vars = vector<Var>(), const Token& t = Token()) : WithToken(t), v(vars) { }
	Vars(const Vars&) = delete;
	vector<Var> v;
	bool isDeclared(uint l) const {
		return std::find_if(v.begin(), v.end(), [l](const Var& v) { return v.lit() == l; }) != v.end();
	}
	void write(ostream& os, const Indent& = Indent()) const override;
};

struct Disj : public Writable, public WithToken {
	struct Pair {
		Pair(uint a, uint b) : v(a < b ? a : b), w(a < b ? b : a) {
			if (a == b) throw Error("single variable cannot be disjointed from itself", Lex::toStr(a));
		}
		uint v;
		uint w;
		bool operator < (const Pair& p) const {
			if (v < p.v) return true;
			else if (v > p.v) return false;
			else return w < p.w;
		}
	};
	typedef vector<unique_ptr<set<uint>>> Vector;

	Disj(const Vector& d = Vector(), const Token& t = Token());
	Disj(const Disj& disj) = delete;

	Vector toVector() const;
	void write(ostream& os, const Indent& = Indent()) const override;
	void check(const Substitution&, Assertion* t = nullptr) const;
	void make_pairs_disjointed(const set<uint>&, const set<uint>&);

	set<Pair> dvars;
};

void parse_expr(Expr& ex);

struct Type : public Writable, public Owner<Type> {
	typedef map<const Type*, unique_ptr<Rule>> Supers;
	Type(Id id, const vector<Id>& sup = vector<Id>(), const Token& t = Token());
	Type(const Type&) = delete;
	vector<User<Type>> sup;
	Supers supers;
	Rules  rules;
	void write(ostream& os, const Indent& i = Indent()) const override;
};

inline bool operator < (const Type& t1, const Type& t2) {
	for (const auto& t : t1.sup) if (t.get() == &t2) return true;
	return false;
}

inline bool operator <= (const Type& t1, const Type& t2) {
	return &t1 == &t2 || t1 < t2;
}

struct Rule : public Writable, public Owner<Rule> {
	Rule(Id i, const Token& t = Token()) : Owner(i.id(), t) { }
	Rule(const Rule&) = delete;
	Vars vars;
	Expr term;
	Type* type() { return term.type.get(); }
	const Type* type() const { return term.type.get(); }
	uint arity() const { return term.tree()->arity(); }
	void write(ostream& os, const Indent& i = Indent()) const override;
};

Rule* find_super(const Type* type, const Type* super);

inline const Type* VarTree::type() const { return type_.get(); }
inline const Type* RuleTree::type() const { return rule->term.type.get(); }

struct Hyp : public Writable, public WithToken {
	Hyp(uint i, const Expr& e = Expr(), const Token& t = Token()) :
		WithToken(t), ind(i), expr(e) { }
	Hyp(uint i, Expr&& e, const Token& t = Token()) :
		WithToken(t), ind(i), expr(std::move(e)) { }
	Hyp(const Hyp&) = delete;
	uint ind;
	Expr expr;
	void write(ostream& os, const Indent& i = Indent()) const override;
};

struct Prop : public Writable, public WithToken {
	Prop(uint i, const Expr& e = Expr(), const Token& t = Token()) :
		WithToken(t), ind(i), expr(e) { }
	Prop(uint i, Expr&& e, const Token& t = Token()) :
		WithToken(t), ind(i), expr(std::move(e)) { }
	Prop(const Prop&) = delete;
	uint ind;
	Expr expr;
	void write(ostream& os, const Indent& i = Indent()) const override;
};

struct Assertion : public Writable, public Owner<Assertion> {
	enum Kind { AXM, THM, DEF };
	Assertion(Id i, const Token& t = Token()) : Owner(i.id(), t) { }
	Assertion(const Assertion&) = delete;
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

struct Axiom : public Assertion {
	Axiom(Id id, const Token& t = Token()) : Assertion(id, t) { }
	Axiom(const Axiom&) = delete;
	Kind kind() const override { return AXM; }
	void write(ostream& os, const Indent& i = Indent()) const override;
};

struct Def : public Assertion {
	Def(Id id, const Token& t = Token()) : Assertion(id, t) { }
	Def(const Def&) = delete;
	Kind kind() const override { return DEF; }
	Expr dfm;
	Expr dfs;
	Expr prop;
	void write(ostream& os, const Indent& i = Indent()) const override;
};

struct Theorem : public Assertion {
	Theorem(Id id, const Token& t = Token()) : Assertion(id, t) { }
	Theorem(const Theorem&) = delete;
	Kind kind() const override { return THM; }
	vector<User<Proof>> proofs;
	void write(ostream& os, const Indent& i = Indent()) const override;
};

struct Ref : public Writable, public WithToken {
	enum Kind { HYP, PROP, STEP };
	Kind kind() const { return static_cast<Kind>(val.index()); }
	Ref(Hyp* h, const Token& t = Token())  : WithToken(t), val(h)  { }
	Ref(Prop* p, const Token& t = Token()) : WithToken(t), val(p)  { }
	Ref(Step* s, const Token& t = Token()) : WithToken(t), val(s)  { }
	Ref(const Ref&) = delete;
	Expr& expr();
	const Expr& expr() const;
	Hyp* hyp() const   { return kind() == HYP  ? std::get<Hyp*>(val) : nullptr; }
	Prop* prop() const { return kind() == PROP ? std::get<Prop*>(val): nullptr; }
	Step* step() const { return kind() == STEP ? std::get<Step*>(val): nullptr; }

	typedef variant<Hyp*, Prop*, Step*> Value;
	Value val;
	void write(ostream& os, const Indent& i = Indent()) const override;
};

// Modes of verification:
//   VERIFY_SUB   verify substitutions,
//   VERIFY_DISJ  verify disjointed restrictions,
//   UPDATE_DISJ  update disjointed restrictions due to verification,
//   VERIFY_QED   verify qed statements
//   VERIFY_DEEP  consider all imported sources
enum Verify {
	VERIFY_SUB   = 0x01,
	VERIFY_DISJ  = 0x02,
	UPDATE_DISJ  = 0x04,
	VERIFY_QED   = 0x08,
	VERIFY_DEEP  = 0x10,
	VERIFY_SRC   = VERIFY_SUB | VERIFY_DISJ | UPDATE_DISJ | VERIFY_QED,
	VERIFY_ALL   = VERIFY_SUB | VERIFY_DISJ | UPDATE_DISJ | VERIFY_QED | VERIFY_DEEP
};

struct Step : public Writable, public WithToken {
	enum Kind { ASS, CLAIM };
	typedef User<Assertion> AssUser;
	typedef unique_ptr<AssUser> AssPtr;
	typedef variant<AssPtr, unique_ptr<Proof>> Value;

	Step(uint i, Step::Kind k, Id id, Proof* p, const Token& t = Token()) :
		WithToken(t), sub(false), ind_(i), proof_(p) {
		if (k == ASS) { val_ = AssPtr(make_unique<AssUser>(id)); }
	}
	Step(const Step&) = delete;
	uint ass_id() const { return std::get<AssPtr>(val_)->id(); }
	//const Token& ass_token() const { return std::get<AssPtr>(val_).get()->token(); }
	Assertion* ass() { return std::get<AssPtr>(val_).get()->get(); }
	Proof* claim() { return std::get<unique_ptr<Proof>>(val_).get(); }
	const Assertion* ass() const { return std::get<AssPtr>(val_).get()->get(); }
	const Proof* claim() const { return std::get<unique_ptr<Proof>>(val_).get(); }
	Proof* proof() { return proof_; }
	const Proof* proof() const { return proof_; }
	Kind kind() const { return static_cast<Kind>(val_.index()); }
	uint ind() const { return ind_; }
	void set_ind(uint ind) { ind_ = ind; }
	void verify(uint mode = VERIFY_ALL) const;
	void write(ostream& os, const Indent& i = Indent()) const override;

	Expr expr;
	vector<unique_ptr<Ref>> refs;
	mutable Substitution sub;

	uint   ind_;
	Value  val_;
	Proof* proof_;
};

typedef DAG<uint> AbstProof;
typedef DAG<const Step*> SubProof;

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

struct Qed : public Writable, public WithToken {
	Qed(Prop* p = nullptr, Step* s = nullptr, const Token& t = Token()) :
		WithToken(t), prop(p), step(s) { }
	Qed(const Qed&) = delete;
	void verify(uint mode = VERIFY_ALL) const;
	Prop* prop;
	Step* step;
	void write(ostream& os, const Indent& i = Indent()) const override;
};

struct Proof : public Writable, public Owner<Proof> {

	enum Kind { VARS, STEP, QED };
	typedef variant<unique_ptr<Vars>, unique_ptr<Step>, unique_ptr<Qed>> Elem;

	static Kind  kind(const Elem& e) { return static_cast<Kind>(e.index()); }
	static Vars* vars(const Elem& e) { return kind(e) == VARS ? std::get<unique_ptr<Vars>>(e).get() : nullptr; }
	static Step* step(const Elem& e) { return kind(e) == STEP ? std::get<unique_ptr<Step>>(e).get() : nullptr; }
	static Qed*  qed(const Elem& e)  { return kind(e) == QED  ? std::get<unique_ptr<Qed>>(e).get()  : nullptr; }

	Proof(Id thm, Id id = Id(), const Token& t = Token());
	Proof(const Proof&) = delete;

	Theorem* theorem() { return dynamic_cast<Theorem*>(thm.get()); }
	const Theorem* theorem() const { return dynamic_cast<const Theorem*>(thm.get()); }
	void verify(uint mode = VERIFY_ALL) const;
	bool check(uint mode = VERIFY_ALL) const;
	vector<Qed*> qeds() const;
	void write(ostream& os, const Indent& i = Indent()) const override;

	Vars            allvars;
	vector<Elem>    elems;
	User<Assertion> thm;
	Proof*          par;
	bool            inner;

};

struct Import : public Writable, public WithToken {
	Import(uint src, const Token& t = Token()) : WithToken(t), source(src) { }
	Import(const Import&) = delete;
	User<Source> source;
	void write(ostream& os, const Indent& i = Indent()) const override;
};

struct Theory : public Writable, public WithToken {
	enum Kind { CONSTANT, TYPE, RULE, AXIOM, DEF, THEOREM, PROOF, THEORY, IMPORT, COMMENT };
	typedef variant<
		unique_ptr<Constant>,
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
		WithToken(t), id(n), nodes(), parent(p) { }
	Theory(const Theory&) = delete;

	void write(ostream& os, const Indent& i = Indent()) const override;
	static Kind kind(const Node& n) { return static_cast<Kind>(n.index()); }
	static Constant* constant(const Node& n) { return std::get<unique_ptr<Constant>>(n).get(); }
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
	Source(const Source&) = delete;
	Token* find(const Token& t);
	void write(ostream& os, const Indent& i = Indent()) const override;

	Theory theory;
};

size_t memvol(const Source&);

void add_to_index(Assertion*);
void add_to_index(Proof*);
Proof* prove(Assertion*);
bool test_with_oracle();

}} // mdl::rus
