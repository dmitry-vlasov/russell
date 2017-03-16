#include <boost/fusion/include/adapt_struct.hpp>

BOOST_FUSION_ADAPT_STRUCT(
	mdl::mm::Section,
	(mdl::mm::Type, type)
	(mdl::string, header)
	(mdl::string, name)
	(mdl::string, footer)
	(mdl::string, contents)
	(mdl::string, root)
	(mdl::string, dir)
	(mdl::string, file)
	(mdl::string, path)
	(mdl::mm::Section*, prev_sect)
	(mdl::mm::Section*, next_sect)
	(mdl::mm::Section*, prev_sibling)
	(mdl::mm::Section*, next_sibling)
	(mdl::mm::Section*, parent)
	(mdl::vector<mdl::mm::Section*>, parts)
)
