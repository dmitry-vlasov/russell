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
	mdl::mm::Proof,
	(std::vector<mdl::mm::Node>, refs)
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
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::mm::Theorem,
	(mdl::uint, label)
	(mdl::Expr, expr)
	(mdl::mm::Proof*, proof)
	(bool, tree)
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
	(std::string, name)
	(std::vector<mdl::mm::Node>, contents)
	(mdl::mm::Block*, parent)
	(uint, ind)
)




