#include <boost/fusion/include/adapt_struct.hpp>

BOOST_FUSION_ADAPT_STRUCT(
	mdl::Symbol,
	(mdl::uint, lit)
	(bool, var)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::Expr,
	(std::vector<mdl::Symbol>, symbols)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::mm::Constants,
	(mdl::Expr, expr)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::mm::Ref::Value,
	(void*, non)
	(mdl::mm::Floating*,  flo)
	(mdl::mm::Essential*, ess)
	(mdl::mm::Axiom*,     ax)
	(mdl::mm::Theorem*,   th)
	(mdl::mm::Proof*,     prf)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::mm::Ref,
	(mdl::mm::Ref::Type, type)
	(mdl::mm::Ref::Value, val)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::mm::Proof,
	(std::vector<mdl::mm::Ref>, refs)
	(mdl::mm::Proof::Type, type)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::mm::Variables,
	(mdl::Expr, expr)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::mm::Disjointed,
	(mdl::Expr, expr)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::mm::Essential,
	(mdl::uint, label)
	(mdl::Expr, expr)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::mm::Floating,
	(mdl::uint, label)
	(mdl::Expr, expr)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::mm::Axiom,
	(mdl::uint, label)
	(mdl::Expr, expr)
	(mdl::uint, arity)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::mm::Theorem,
	(mdl::uint, label)
	(mdl::Expr, expr)
	(mdl::uint, arity)
	(mdl::mm::Proof*, proof)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::mm::Node::Value,
	(mdl::mm::Constants*,  cst)
	(mdl::mm::Variables*,  var)
	(mdl::mm::Disjointed*, dis)
	(mdl::mm::Floating*,   flo)
	(mdl::mm::Essential*,  ess)
	(mdl::mm::Axiom*,      ax)
	(mdl::mm::Theorem*,    th)
	(mdl::mm::Block*,      blk)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::mm::Node,
	(mdl::uint, type)
	(mdl::mm::Node::Type, type)
	(mdl::mm::Node::Value, val)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::mm::Block,
	(std::vector<mdl::mm::Node>, contents)
	(mdl::mm::Block*, parent)
	(uint, ind)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::mm::Source,
	(std::string, name)
	(mdl::mm::Block*, block)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::mm::Inclusion,
	(mdl::mm::Source*, source)
	(bool,            primary)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::mm::Comment,
	(std::string, text)
)

