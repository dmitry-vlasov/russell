#include <boost/fusion/include/adapt_struct.hpp>

BOOST_FUSION_ADAPT_STRUCT(
	mdl::mm::cut::Section,
	(mdl::mm::cut::Type, type)
	(mdl::string, header)
	(mdl::string, name)
	(mdl::string, footer)
	(mdl::string, contents)
	(mdl::string, root)
	(mdl::string, dir)
	(mdl::string, file)
	(mdl::string, path)
	(mdl::mm::cut::Section*, prev_sect)
	(mdl::mm::cut::Section*, next_sect)
	(mdl::mm::cut::Section*, prev_sibling)
	(mdl::mm::cut::Section*, next_sibling)
	(mdl::mm::cut::Section*, parent)
	(mdl::vector<mdl::mm::cut::Section*>, parts)
)
