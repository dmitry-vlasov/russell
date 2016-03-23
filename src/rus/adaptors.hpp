#include <boost/fusion/include/adapt_struct.hpp>

BOOST_FUSION_ADAPT_STRUCT(
	mdl::Symbol,
	(uint, lit)
	(bool, var)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::Expr,
	(std::vector<mdl::Symbol>, symbols)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Symbol,
	(uint, lit)
	(bool, rep)
	(mdl::rus::Type*, type)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Const,
	(mdl::rus::Symbol, symb)
	(mdl::rus::Symbol, ascii)
	(mdl::rus::Symbol, latex)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Vars,
	(mdl::vector<mdl::rus::Symbol>, v)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Disj,
	(mdl::vector<mdl::vector<mdl::rus::Symbol>>, d)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Type,
	(mdl::uint, id)
	(mdl::vector<mdl::rus::Type*>,    sup)
	(mdl::rus::Tree<mdl::rus::Rule*>, rules)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Rule,
	(mdl::uint, id)
	(mdl::rus::Type*, type)
	(mdl::rus::Vars, vars)
	(mdl::rus::Expr, term)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Hyp,
	(uint, ind)
	(mdl::rus::Expr, expr)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Prop,
	(uint, ind)
	(mdl::rus::Expr, expr)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Assertion,
	(uint, id)
	(mdl::rus::Vars, vars)
	(mdl::rus::Disj, disj)
	(mdl::vector<mdl::rus::Hyp*>,  hyps)
	(mdl::vector<mdl::rus::Prop*>, props)
	(mdl::Location,  loc)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Axiom,
	(mdl::rus::Assertion, ass)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Def,
	(mdl::rus::Assertion, ass)
	(mdl::rus::Assertion, def)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Theorem,
	(mdl::rus::Assertion, ass)
	(std::vector<mdl::rus::Proof*>, proofs)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Ref::Value,
	(void*,  non)
	(mdl::rus::Hyp*,   hyp)
	(mdl::rus::Prop*,  prop)
	(mdl::rus::Step*,  step)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Ref,
	(mdl::rus::Ref::Kind, kind)
	(mdl::rus::Ref::Value, val)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Step::Ass,
	(void*,  non)
	(mdl::rus::Axiom*,   axm)
	(mdl::rus::Def*,     def)
	(mdl::rus::Theorem*, thm)
	(mdl::rus::Proof*, thm)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Step,
	(uint, ind)
	(mdl::rus::Expr, expr)
	(mdl::rus::Step::Kind, kind)
	(mdl::rus::Step::Ass, ass)
	(mdl::vector<mdl::rus::Ref>, refs)
	(mdl::rus::Proof*, proof)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Qed,
	(mdl::rus::Prop*, prop)
	(mdl::rus::Step*, step)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Proof::Elem::Value,
	(void*, non)
	(mdl::rus::Vars*, vars)
	(mdl::rus::Step*, step)
	(mdl::rus::Qed*,  qed)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Proof::Elem,
	(mdl::rus::Proof::Elem::Kind, kind)
	(mdl::rus::Proof::Elem::Value, val)
)


BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Proof,
	(uint, id)
	(mdl::rus::Vars, vars)
	(mdl::vector<mdl::rus::Proof::Elem>, elems)
	(mdl::rus::Theorem*, thm)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Node::Value,
	(void*,      non)
	(mdl::rus::Const*,   cst)
	(mdl::rus::Type*,    tp)
	(mdl::rus::Rule*,    rul)
	(mdl::rus::Axiom*,   ax)
	(mdl::rus::Def*,     def)
	(mdl::rus::Theorem*, thm)
	(mdl::rus::Proof*,   prf)
	(mdl::rus::Theory*,  thy)
	(mdl::rus::Import*,  imp)
)


BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Node,
	(mdl::rus::Node::Kind, kind)
	(mdl::rus::Node::Value, val)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Import,
	(mdl::string, path)
	(mdl::rus::Source*, source)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Theory,
	(uint, id)
	(mdl::vector<mdl::rus::Node>, nodes)
	(mdl::rus::Theory*, parent)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Source,
	(bool, top)
	(mdl::string, name)
	(mdl::rus::Theory, theory)
)




