#include <boost/python/class.hpp>
#include <boost/python/module.hpp>
#include <boost/python/def.hpp>
#include <boost/python/self.hpp>

#include "smm/ast.hpp"

namespace mdl {

void add_symbol(Expr& ex, Symbol s) {
	ex += s;
}

}

BOOST_PYTHON_MODULE(pymdl) {

    using namespace boost::python;
    class_<mdl::Symbol>("Symbol")
    	.def(init<mdl::uint>())
    	.def(init<mdl::uint, bool>())
        .def_readwrite("lit", &mdl::Symbol::lit)
		.def_readwrite("var", &mdl::Symbol::var)
//		.def(self == self)
//		.def(self != self)
//		.def(self < self)
//		.def(str(self))
        ;
/*
    class_<mdl::Expr>("Expr")
    	.def(init<const mdl::Expr&>())
        .def("symbols", &mdl::Expr::symbols)
//		.def(self == self)
//		.def(self != self)
//		.def(str(self))
        ;
*/
    def("add_symbol", mdl::add_symbol);

}
