#include <boost/fusion/include/adapt_struct.hpp>

BOOST_FUSION_ADAPT_STRUCT(
	mdl::mm2::Section,
	(mdl::mm2::Type, type)
	(mdl::string, header)
	(mdl::string, name)
	(mdl::string, footer)
	(mdl::string, contents)
	(mdl::string, root)
	(mdl::string, dir)
	(mdl::string, file)
	(mdl::string, path)
	(mdl::mm2::Section*, prev_sect)
	(mdl::mm2::Section*, next_sect)
	(mdl::mm2::Section*, prev_sibling)
	(mdl::mm2::Section*, next_sibling)
	(mdl::mm2::Section*, parent)
	(mdl::vector<mdl::mm2::Section*>, parts)
)
