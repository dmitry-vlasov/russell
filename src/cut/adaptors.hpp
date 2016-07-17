#include <boost/fusion/include/adapt_struct.hpp>

BOOST_FUSION_ADAPT_STRUCT(
	mdl::cut::Section,
	(mdl::cut::Type, type)
	(mdl::string, header)
	(mdl::string, name)
	(mdl::string, footer)
	(mdl::string, contents)
	(mdl::string, dir)
	(mdl::string, file)
	(mdl::string, path)
	(mdl::cut::Section*, prev_sect)
	(mdl::cut::Section*, next_sect)
	(mdl::cut::Section*, prev_sibling)
	(mdl::cut::Section*, next_sibling)
	(mdl::cut::Section*, parent)
	(mdl::vector<mdl::cut::Section*>, parts)
)
