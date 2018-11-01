/*
    Copyright (c) 2016 Juraj Major

    This file is part of LTL3TELA.

    LTL3TELA is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    LTL3TELA is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with LTL3TELA.  If not, see <http://www.gnu.org/licenses/>.
*/

#ifndef SEMIDETERMINISTIC_H
#define SEMIDETERMINISTIC_H
#include <spot/tl/print.hh>
#include <spot/twaalgos/cleanacc.hh>
#include <spot/twaalgos/hoa.hh>
#include <spot/twaalgos/postproc.hh>
#include <spot/twaalgos/simulation.hh>
#include <spot/twaalgos/sccfilter.hh>
#include <spot/twaalgos/alternation.hh>
#include <spot/parseaut/public.hh>
#include <spot/twaalgos/reachiter.hh>
#include <spot/twa/bddprint.hh>
#include <iostream>
#include <sstream>
#include <string>
#include <map>
#include "automaton.hpp"

// turns the given VWAA into an equivalent semideterministic
// automaton in the Spot's structure
spot::twa_graph_ptr make_semideterministic(VWAA *vwaa);

bool checkMayReachableStates(std::shared_ptr<spot::twa_graph> vwaa, std::set<std::string> Conf, std::set<std::string> Valid, bool isqmay[]);
void addToValid(std::shared_ptr<spot::twa_graph> vwaa, std::string q, std::set<std::string> &Valid);
void createR(std::shared_ptr<spot::twa_graph> vwaa, std::set<std::string> Conf, std::set<std::string> R,  bool isqmay[], bool isqmust[]);
#endif
