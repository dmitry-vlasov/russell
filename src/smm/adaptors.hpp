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
	mdl::smm::Constants,
	(mdl::Expr, expr)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::smm::Ref,
	(mdl::smm::Ref::Type, type)
	(uint, index)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::smm::Proof,
	(std::vector<mdl::smm::Ref>, refs)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::smm::Variables,
	(mdl::Expr, expr)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::smm::Disjointed,
	(mdl::Expr, expr)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::smm::Essential,
	(uint, index)
	(mdl::Expr, expr)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::smm::Floating,
	(uint, index)
	(mdl::Expr, expr)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::smm::Inner,
	(uint, index)
	(mdl::Expr, expr)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::smm::Proposition,
	(bool, axiom)
	(uint, label)
	(mdl::Expr, expr)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::smm::Assertion,
	(std::vector<mdl::smm::Variables>, variables)
	(std::vector<mdl::smm::Disjointed>, disjointed)
	(std::vector<mdl::smm::Essential>, essential)
	(std::vector<mdl::smm::Floating>, floating)
	(std::vector<mdl::smm::Inner>, inner)
	(mdl::smm::Proposition, prop)
	(mdl::smm::Proof*, proof)
	(mdl::Location, loc)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::smm::Source,
	(bool, top)
	(std::string, name)
	(std::vector<mdl::smm::Source::Node>, contents)
)




