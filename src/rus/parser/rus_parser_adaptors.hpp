
BOOST_FUSION_ADAPT_STRUCT(
	mdl::Symbol,
	(mdl::uint, lit)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Expr,
	(mdl::rus::User<mdl::rus::Type>, type)
	(mdl::rus::Tree*, tree)
	(mdl::vector<mdl::rus::Symbol>, symbols)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Symbol,
	(mdl::uint, lit)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Comment,
	(mdl::string,     text)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Const,
	(mdl::rus::Symbol, symb)
	(mdl::rus::Symbol, ascii)
	(mdl::rus::Symbol, latex)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Vars,
	(mdl::vector<mdl::rus::Symbol>, v)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Disj,
	(mdl::vector<mdl::vector<mdl::rus::Symbol>>, d)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Type,
	(mdl::uint, id)
	(mdl::vector<mdl::rus::Type*>, sup)
	(mdl::rus::Type::Supers, supers)
	(mdl::rus::Rules, rules)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Rule,
	(mdl::uint, id)
	(mdl::rus::Vars, vars)
	(mdl::rus::Expr, term)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Hyp,
	(mdl::uint, ind)
	(mdl::rus::Expr, expr)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Prop,
	(mdl::uint, ind)
	(mdl::rus::Expr, expr)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Axiom,
	(mdl::rus::Vars, vars)
	(mdl::rus::Disj, disj)
	(mdl::vector<mdl::rus::Hyp*>,  hyps)
	(mdl::vector<mdl::rus::Prop*>, props)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Def,
	(mdl::rus::Vars, vars)
	(mdl::rus::Disj, disj)
	(mdl::vector<mdl::rus::Hyp*>,  hyps)
	(mdl::rus::Expr, dfm)
	(mdl::rus::Expr, dfs)
	(mdl::rus::Expr, prop)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Theorem,
	(mdl::rus::Vars, vars)
	(mdl::rus::Disj, disj)
	(mdl::vector<mdl::rus::Hyp*>,  hyps)
	(mdl::vector<mdl::rus::Prop*>, props)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Ref::Value,
	(void*,  non)
	(mdl::rus::Hyp*,   hyp)
	(mdl::rus::Prop*,  prop)
	(mdl::rus::Step*,  step)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Ref,
	(mdl::rus::Ref::Kind, kind)
	(mdl::rus::Ref::Value, val)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Step::Value,
	(void*,  non)
	(mdl::rus::Assertion*, ass)
	(mdl::rus::Proof*,     thm)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Step,
	(mdl::uint, ind)
	(mdl::rus::Expr, expr)
	(mdl::rus::Step::Kind, kind)
	(mdl::rus::Step::Value, val)
	(mdl::vector<mdl::rus::Ref*>, refs)
	(mdl::rus::Proof*, proof)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Qed,
	(mdl::rus::Prop*, prop)
	(mdl::rus::Step*, step)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Proof::Elem::Value,
	(void*, non)
	(mdl::rus::Vars*, vars)
	(mdl::rus::Step*, step)
	(mdl::rus::Qed*,  qed)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Proof::Elem,
	(mdl::rus::Proof::Elem::Kind, kind)
	(mdl::rus::Proof::Elem::Value, val)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Proof,
	(mdl::uint, id)
	(mdl::rus::Vars, vars)
	(mdl::vector<mdl::rus::Proof::Elem>, elems)
	(mdl::rus::Theorem*, thm)
	(mdl::rus::Proof*, par)
	(bool, has_id)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Node::Value,
	(void*,      non)
	(mdl::rus::Const*,   cst)
	(mdl::rus::Type*,    tp)
	(mdl::rus::Rule*,    rul)
	(mdl::rus::Axiom*,   ax)
	(mdl::rus::Def*,     def)
	(mdl::rus::Theorem*, thm)
	(mdl::rus::Proof*,   prf)
	(mdl::rus::Theory*,  thy)
	(mdl::rus::Import*,  imp)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Node,
	(mdl::rus::Node::Kind, kind)
	(mdl::rus::Node::Value, val)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Import,
	(mdl::rus::Source*, source)
	(bool, primary)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Theory,
	(mdl::uint, id)
	(mdl::vector<mdl::rus::Node>, nodes)
	(mdl::rus::Theory*, parent)
)

BOOST_FUSION_ADAPT_STRUCT(
	mdl::rus::Source,
	(mdl::rus::Theory*, theory)
)



