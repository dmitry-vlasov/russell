#include <rus_ast.hpp>
#include <rus/prover/unify/rus_prover_unify_index.hpp>
#include <rus/prover/rus_prover_maker.hpp>

namespace mdl { namespace rus { namespace {

void generalize_theorems(Theorem* thm, std::atomic<int>& counter) {
	//cout << (i == -1 ? "" : to_string(i) + " ")  << "testing proof maker of " << show_id(p->theorem->id()) << " ... " << std::flush;
	AbstProof abstProof = thm->proof->abst();
	unique_ptr<Theorem> gen_thm = prover::make_theorem(abstProof, Lex::toInt("gen_" + Lex::toStr(thm->id())));
	try {
		vector<Substitution> matches1 = match(*gen_thm, *thm);
		if (!matches1.size()) {
			string err;
			err += "wrong proof remaked\n";
			err += "ret.theorem:\n" + gen_thm->show() + "\n";
			err += "p->theorem:\n" + thm->show() + "\n";
			throw Error(err);
		}
		vector<Substitution> matches2 = match(*thm, *gen_thm);
		if (!matches2.size()) {
			beautify(*gen_thm);
			gen_thm->token = thm->token;
			Source* src = Sys::mod().math.get<Source>().access(thm->token.src()->id());
			uint pos = -1;
			for (uint i = 0; i < src->theory.nodes.size(); ++i) {
				const Theory::Node& n = src->theory.nodes.at(i);
				const Writable* w = Theory::get(n);
				if (const WithToken* t = dynamic_cast<const WithToken*>(w)) {
					if (t->token == thm->token) {
						pos = i;
						break;
					}
				}

			}

			cout << "strongly more general theorem" << endl;
			cout << "more general:\n" << gen_thm->show() << endl;
			cout << "original:\n" << thm->show() << endl;
			if (pos == -1) {
				throw Error("theorem " + Lex::toStr(thm->id()) + " couldn't be located");
			}
			src->theory.insert(gen_thm.release(), pos);

			counter.store(counter.load() + 1);
		}
	} catch (Timeout& timeout) {
		cout << timeout.what();
	}
}

}

#ifdef PARALLEL
#define PARALLEL_GENERALIZE_THEOREMS
#endif

void generalize_theorems(const string& opts)  {
	map<string, string> parsed_opts = parse_options(opts);
	uint theorem = parsed_opts.count("theorem") ? Lex::toInt(parsed_opts.at("theorem")) : -1;

	std::atomic<int> counter(0);
	vector<Theorem*> theorems;
	for (auto& a : Sys::mod().math.get<Assertion>()) {
		if (Theorem* thm = dynamic_cast<Theorem*>(a.second.data)) {
			if (thm->proof) {
				if (theorem == -1 || thm->id() == theorem) {
					theorems.push_back(thm);
				}
			}
		}
	}
#ifdef PARALLEL_GENERALIZE_THEOREMS
	tbb::parallel_for (tbb::blocked_range<size_t>(0, theorems.size()),
		[&theorems, &counter] (const tbb::blocked_range<size_t>& r) {
			for (size_t i = r.begin(); i != r.end(); ++i) {
				generalize_theorems(theorems[i], counter);
			}
		}
	);
#else
	for (auto th : theorems) {
		generalize_theorems(th, counter);
	}
#endif
	if (counter.load() > 0) {
		cout << "totally generalized theorems: " << counter.load() << endl;
	}
}

}} // mdl::rus
