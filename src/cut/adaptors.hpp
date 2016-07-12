#include <boost/fusion/include/adapt_struct.hpp>

BOOST_FUSION_ADAPT_STRUCT(
	mdl::cut::Paragraph,
	(mdl::string, file)
	(mdl::string, name)
	(mdl::string, descr)
	(mdl::string, contents)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::cut::Chapter,
	(mdl::string, file)
	(mdl::string, name)
	(mdl::string, descr)
	(mdl::string, contents)
	(mdl::vector<mdl::cut::Paragraph*>, paragraphs)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::cut::Part,
	(mdl::string, file)
	(mdl::string, name)
	(mdl::string, descr)
	(mdl::string, contents)
	(mdl::vector<mdl::cut::Chapter*>, chapters)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::cut::Source,
	(mdl::string, file)
	(mdl::string, name)
	(mdl::string, descr)
	(mdl::string, contents)
	(mdl::vector<mdl::cut::Part*>, parts)
)


