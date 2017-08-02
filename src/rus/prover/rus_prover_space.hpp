#pragma once

#include "rus_prover_index.hpp"

namespace mdl { namespace rus { namespace prover {

struct HypRef {
	User<Assertion> ass;
	uint hyp;
};

struct Space {
	set<Prop*>    leaf_props;
	set<Hyp*>     leaf_hyps;
	Hyp           root;
	PropRef       prop;
	Index<HypRef> hyps;

	Space(rus::Qed*);
	void buildUp(Prop*);
	void buildUp(Hyp*);
};

}}}

