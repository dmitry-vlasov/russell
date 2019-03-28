#include "mm_ast.hpp"
#include "mm_sys.hpp"

namespace mdl { namespace mm { namespace {

bool has_contents(const Source* s) {
	bool has = false;
	for (const auto& n : s->contents) {
		if (Source::kind(n) == Source::ASSERTION || Source::kind(n) == Source::CONST) {
			has = true;
			break;
		}
	}
	return has;
}

void collect_included_labels(uint label, const Expr& expr, set<uint>& deps, const map<uint, set<uint>>& rule_deps) {
	const map<uint, uint>& consts = Sys::get().math.consts;
	Literal first = expr.front();
	for (const auto& s : expr) {
		if (s == first) continue;
		auto rit = rule_deps.find(s.lit);
		if (rit != rule_deps.end()) {
			for (uint src_id : (*rit).second) {
				if (src_id != label) {
					deps.insert(src_id);
				}
			}
		}
		auto cit = consts.find(s.lit);
		if (cit != consts.end()) {
			uint src_id = (*cit).second;
			if (src_id != label) {
				deps.insert(src_id);
			}
		}
	}
}

void collect_included_labels(uint label, const Assertion* ass, set<uint>& deps, const map<uint, set<uint>>& rule_deps) {
	for (const auto& ref : ass->proof.refs) {
		if (ref.is_assertion()) {
			if (!ref.ass()) {
				string msg("\n");
				msg += "ref: " + Lex::toStr(ref.label()) + "\n";
				msg += "theorem: " + Lex::toStr(ass->id()) + "\n";
				msg += "source: " + Lex::toStr(ass->token.src()->id()) + "\n";
				throw Error("unresolved ref", msg);
			}
			uint src_id = ref.ass()->token.src()->id();
			if (src_id != label) {
				deps.insert(src_id);
			}
		}
	}
	collect_included_labels(label, ass->expr, deps, rule_deps);
	for (const auto& h : ass->hyps) {
		collect_included_labels(label, h.get()->expr, deps, rule_deps);
	}
}

set<uint> minimize_deps(uint label, const set<uint>& deps, map<uint, set<uint>>& resolved) {
	set<uint> minimized;
	set<uint> cumulative;
	for (uint dep : deps) {
		if (!cumulative.count(dep)) {
			minimized.insert(dep);
		}
		cumulative.insert(dep);
		for (uint d : resolved[dep]) {
			cumulative.insert(d);
		}
	}
	resolved[label] = cumulative;
	while (true) {
		uint redundant = -1;
		for (uint dep_1 : minimized) {
			for (uint dep_2 : minimized) {
				if (dep_1 != dep_2) {
					if (resolved[dep_2].count(dep_1)) {
						redundant = dep_1;
						break;
					} else if (resolved[dep_1].count(dep_2)) {
						redundant = dep_2;
						break;
					}
				}
			}
			if (redundant != -1) {
				minimized.erase(redundant);
				break;
			}
		}
		if (redundant == -1) {
			break;
		}
	}
	return minimized;
}

void minimize_imports(uint label, map<uint, set<uint>>& resolved, const map<uint, set<uint>>& rule_deps) {
	Source* s = Sys::mod().math.get<Source>().access(label);
	if (has_contents(s)) {
		set<uint> deps;
		for (const auto& n : s->contents) {
			if (Source::kind(n) == Source::IMPORT) {
				Import* imp = std::get<unique_ptr<Import>>(n).get();
				uint imported_id = imp->source.id();
				if (!resolved.count(imported_id)) {
					minimize_imports(imported_id, resolved, rule_deps);
				}
			}
			if (Source::kind(n) == Source::ASSERTION) {
				Assertion* ass = std::get<unique_ptr<Assertion>>(n).get();
				collect_included_labels(label, ass, deps, rule_deps);
			}
		}
		if (deps.size()) {
			set<uint> minimized = minimize_deps(label, deps, resolved);
			vector<Source::Node> new_contents;
			for (uint inc : minimized) {
				new_contents.emplace_back(unique_ptr<Import>(new Import(inc, Token(s))));
			}
			for (auto& n : s->contents) {
				switch (Source::kind(n)) {
				case Source::IMPORT: break;
				case Source::COMMENT:   new_contents.emplace_back(unique_ptr<Comment>(std::get<unique_ptr<Comment>>(n).release())); break;
				case Source::CONST:     new_contents.emplace_back(unique_ptr<Const>(std::get<unique_ptr<Const>>(n).release())); break;
				case Source::ASSERTION: new_contents.emplace_back(unique_ptr<Assertion>(std::get<unique_ptr<Assertion>>(n).release())); break;
				}
			}
			s->contents = std::move(new_contents);
		}
	} else {
		resolved[label];
		for (const auto& n : s->contents) {
			if (Source::kind(n) == Source::IMPORT) {
				Import* imp = std::get<unique_ptr<Import>>(n).get();
				uint imported_id = imp->source.id();
				if (!resolved.count(imported_id)) {
					minimize_imports(imported_id, resolved, rule_deps);
				}
			}
		}
	}
}

map<uint, set<uint>> create_rule_deps() {
	vector<const Assertion*> rules;
	for (const auto& p : Sys::get().math.get<Assertion>()) {
		const Assertion* a = p.second.data;
		Literal first = a->expr.front();
		if (!first.is_turnstile()) {
			rules.push_back(a);
		}
	}

	map<uint, set<uint>> rule_deps;
	for (auto a : rules) {
		Literal first = a->expr.front();
		if (!first.is_turnstile()) {
			for (auto s : a->expr) {
				if (!s.var && s != first) {
					bool is_unique = true;
					for (auto b : rules) {
						if (a == b) continue;
						for (auto t : b->expr) {
							if (t == b->expr.front()) continue;
							if (t == s) {
								is_unique = false;
								break;
							}
						}
						if (!is_unique) {
							break;
						}
					}
					if (is_unique) {
						rule_deps[s.lit].insert(a->token.src()->id());
					}
				}
			}
		}
	}
	for (const auto& p : rule_deps) {
		uint rule_symb = p.first;
		cout << Lex::toStr(p.first) << ":" << endl;
		for (uint s : p.second) {
			cout << "\t" << Lex::toStr(s) << endl;
		}
	}
	cout << endl;
	return rule_deps;
}

}

void minimize_imports(uint label) {
	Sys::timer()["minimize"].start();
	map<uint, set<uint>> resolved;
	map<uint, set<uint>> rule_deps = std::move(create_rule_deps());
	minimize_imports(label, resolved, rule_deps);
	Sys::timer()["minimize"].start();
}

}} // mdl::mm2
