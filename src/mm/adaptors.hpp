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
	mdl::mm::Constants,
	(mdl::Expr, expr)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::mm::Ref,
	(mdl::mm::Node, node)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::mm::Proof,
	(std::vector<mdl::mm::Ref>, refs)
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
	(uint, index)
	(mdl::Expr, expr)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::mm::Floating,
	(uint, index)
	(mdl::Expr, expr)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::mm::Axiom,
	(uint, label)
	(mdl::Expr, expr)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::mm::Theorem,
	(uint, label)
	(mdl::Expr, expr)
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
	(mdl::mm::Node::Type, type)
	(mdl::mm::Node::Value, val)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::mm::Block,
	(bool, top)
	(std::string, name)
	(std::vector<mdl::mm::Node>, contents)
)




