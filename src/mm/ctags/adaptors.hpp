#include <boost/fusion/include/adapt_struct.hpp>

BOOST_FUSION_ADAPT_STRUCT(
	mdl::mm::Source,
	(std::string, root)
	(std::string, name)
	(mdl::set<mdl::mm::ctags::Tag>, tags)
)

