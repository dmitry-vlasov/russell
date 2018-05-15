#include <mm2_ast.hpp>
#include <mm2_sys.hpp>

namespace mdl { namespace mm2 { namespace {

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

void collect_included_labels(uint label, const Assertion* ass, set<uint>& deps) {
	for (const auto& ref : ass->proof.refs) {
		if (ref.is_assertion()) {
			uint src_id = ref.ass()->token.src()->id();
			if (src_id != label) {
				deps.insert(src_id);
			}
		}
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

void minimize_imports(uint label, map<uint, set<uint>>& resolved) {
	Source* s = Sys::mod().math.get<Source>().access(label);
	if (has_contents(s)) {
		set<uint> deps;
		for (const auto& n : s->contents) {
			if (Source::kind(n) == Source::IMPORT) {
				Import* imp = std::get<unique_ptr<Import>>(n).get();
				uint imported_id = imp->source.id();
				if (!resolved.count(imported_id)) {
					minimize_imports(imported_id, resolved);
				}
			}
			if (Source::kind(n) == Source::ASSERTION) {
				Assertion* ass = std::get<unique_ptr<Assertion>>(n).get();
				collect_included_labels(label, ass, deps);
			}
		}
		if (deps.size()) {
			set<uint> minimized = minimize_deps(label, deps, resolved);
			vector<Source::Node> new_contents;
			for (uint inc : minimized) {
				new_contents.emplace_back(unique_ptr<Import>(new Import(inc)));
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
					minimize_imports(imported_id, resolved);
				}
			}
		}
	}
}

}

void minimize_imports(uint label) {
	Sys::timer()["minimize"].start();
	map<uint, set<uint>> resolved;
	minimize_imports(label, resolved);
	Sys::timer()["minimize"].start();
}

}} // mdl::mm2
