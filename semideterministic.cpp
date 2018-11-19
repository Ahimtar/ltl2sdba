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

#include "semideterministic.hpp"

std::vector<bdd> gAlphabet;

// Converts a given VWAA to sDBA;
spot::twa_graph_ptr make_semideterministic(VWAA *vwaa, std::string debug) {

    // We first transform the VWAA into spot format

    // Creating helper files and saving current stream buffer
    std::ofstream outs;
    std::streambuf *coutbuf = std::cout.rdbuf();

    // Redirecting output into helper file and printing vwaa in hoa
    outs.open ("helper.hoa", std::ofstream::trunc);
    std::cout.rdbuf(outs.rdbuf());
    vwaa->print_hoaf();
    std::cout.rdbuf(coutbuf);
    outs.close();

    // Parsing the helper, acquiring spot format
    spot::parsed_aut_ptr pvwaaptr = parse_aut("helper.hoa", spot::make_bdd_dict());
    if (pvwaaptr->format_errors(std::cerr))
        return vwaa->spot_aut;  // todo Better error message
    if (pvwaaptr->aborted)
    {
        std::cerr << "--ABORT-- read\n";
        return vwaa->spot_aut;  // todo Better error message
    }
    auto pvwaa = pvwaaptr->aut;


    // We have VWAA parsed. Now, we assign Qmays and Qmusts and remove acceptance marks

    int nq = pvwaa->num_states();

    const spot::bdd_dict_ptr& dict = pvwaa->get_dict();

    bool isqmay[nq];
    bool isqmust[nq];

    auto snvwaa = pvwaa->get_named_prop<std::vector<std::string>>("state-names");

    // We iterate over all states of the VWAA
    for (unsigned q = 0; q < nq; ++q)
    {
        if (debug == "1"){std::cout << "State: " << (*snvwaa)[q] << " (" << q << ").\n";}
        // Renaming state to its number instead of the LTL formula for later use
        (*snvwaa)[q] = std::to_string(q);

        isqmay[q] = false;
        bool thereIsALoop = false;
        // If there exists a looping, but not accepting outgoing edge, we set this state as Qmay
        for (auto& t: pvwaa->out(q))
        {
            for (unsigned d: pvwaa->univ_dests(t.dst))
            {
                if (t.src == d && t.acc.id == 0) {
                    isqmay[q] = true;
                    if (debug == "1"){std::cout << "It's Qmay. ";} // It also may be Qmust
                    thereIsALoop = true;
                    break;
                }
            }
            if (thereIsALoop){ break; }
        }

        isqmust[q] = true;
        // If we find an outgoing edge, where there is no loop, we set this state as not Qmust and break the loop
        for (auto& t: pvwaa->out(q))
        {
            thereIsALoop = false;
            for (unsigned d: pvwaa->univ_dests(t.dst))
            {
                if (t.src == d){
                    thereIsALoop = true;
                }
            }
            if (!thereIsALoop){
                isqmust[q] = false;
                if (debug == "1"){std::cout << "It's not Qmust. ";} // If this is not printed, it is Qmust
                break;
            }
        }

        // Setting acceptance

        // Since we only work with "yes / no" acceptance, we can use the numbers differently:
        //  {} = 0 Means edge is not accepting
        // {0} = 1 Means edge is accepting
        // {1} = 2 Means edge was accepting in vwaa, but will not be accepting in sdba
        // We remove acceptance marks from all the edges, since no edge in the nondeterministic part is accepting
        for (auto& t: pvwaa->out(q))
        {
            for (unsigned d: pvwaa->univ_dests(t.dst)) {
                if (debug == "1") {
                    std::cout << "\nEdge " << t.src << "-" << d << " accepting labels: " << t.acc << ". ";
                }
                if (t.acc != 0) {
                    t.acc = 2;
                    if (debug == "1") { std::cout << "We set acc to " << t.acc << ". "; }
                }
            }
        }
        if (debug == "1"){std::cout << "\n";}

        // todo how to handle automata that dont accept at all? do we need to bother with them?
    }

    // In gAlphabet variable, we store the set of all edge labels
    // (not only "a", "b", but also "and"-formulae: "a&b". not "a|b".)
    // Here, we create the alphabet by adding all possible labels using power-set construction

    // pow(2, pvwaa->ap().size()) is the amount of all combinations of labels = num of letters in the final alphabet
    for (int i = 0; i < pow(2, pvwaa->ap().size()); i++){
        bdd thisbdd = bdd_true();
        // for all digits in the binary form of i
        for (int digit = 0; digit < pvwaa->ap().size(); digit++){
            if ((i & (int)pow(2, digit)) != 0){
                // add atomic proposition number digit
                thisbdd = bdd_and(thisbdd, bdd_ithvar(digit));
            } else {
                thisbdd = bdd_and(thisbdd, bdd_not(bdd_ithvar(digit)));
            }
        }
        gAlphabet.push_back(thisbdd);
    }

   /* std::cout << "THIS: " << pvwaa->prop_state_acc() << "\n";
    pvwaa->prop_state_acc(false);
    //pvwaa->prop_universal(spot::trival::value_t::no_value);
    //pvwaa->prop_complete(spot::trival::value_t::no_value); // todo remove this once we make edges in the deterministic part

    if (pvwaa->prop_state_acc() == spot::trival::value_t::yes_value){
        std::cout << "y: " << pvwaa->prop_state_acc() << "\n";
    } else {
        std::cout << "n: " << pvwaa->prop_state_acc() << "\n";
    }

*/
    // We now start building the SDBA by removing alternation, which gives us the final nondeterministic part
    spot::twa_graph_ptr sdba = spot::remove_alternation(pvwaa, true);

    /*//std::cout << "THISdba: " << sdba->prop_state_acc() << "\n";
    sdba->prop_state_acc(spot::trival::value_t::no_value);
    sdba->prop_universal(spot::trival::value_t::no_value);
    sdba->prop_complete(spot::trival::value_t::no_value); // todo remove this once we make edges in the deterministic part

    if (sdba->prop_state_acc() == spot::trival::value_t::yes_value){
        std::cout << "y: " << sdba->prop_state_acc() << "\n";
    } else {
        std::cout << "n: " << sdba->prop_state_acc() << "\n";
    }*/


    // Definition of the phis and Rs assigned to the states in the deterministic part, for future
    std::map<unsigned, std::set<std::string>> Rname;
    std::map<unsigned, std::set<unsigned>> phi1;
    std::map<unsigned, std::set<unsigned>> phi2;

    unsigned nc = sdba->num_states(); // Number of configurations C (states in the nondeterministic part)

    // State-names C are in style of "1,2,3", these represent states Q of the former VWAA configuration
    auto sn = sdba->get_named_prop<std::vector<std::string>>("state-names");
    std::set<std::string> C[nc];

    // We mark the Rs of the states of ND part so we differ them from D part states with empty R, phi1 and phi2 later on
    for (unsigned ci = 0; ci < nc; ++ci) {
        Rname[ci] = {"ND-part state"};
    }

    // Choosing the R

    // We go through all the states in C
    // In each one, we go through all its Q-s and build all possible R-s based on what types of states Q-s are
    // For each R - if it is a new R, we build an R-component
    for (unsigned ci = 0; ci < nc; ++ci) {

        // We parse the statename ((*sn)[ci]) to create a set of states
        if (sn && ci < sn->size() && !(*sn)[ci].empty()) {
            std::string s = ((*sn)[ci]) + ",";
            std::string delimiter = ",";
            size_t pos = 0;
            std::string token;
            while ((pos = s.find(delimiter)) != std::string::npos) {
                token = s.substr(0, pos);
                C[ci].insert(token);
                s.erase(0, pos + delimiter.length());
            }
        } else {
            std::cout << "Wrong C state name."; // todo better error message
        }

        std::set<std::string> R;

        if (debug == "1"){std::cout << "\nChecking if this configuration contains only valid states: " << ci << "\n";}
        // Check if only states reachable from Qmays are in C. If not, this configuration can not contain an R.
        if (checkMayReachableStates(pvwaa, C[ci], R, isqmay)){  // We are using R just as a placeholder empty set here
            R.clear();
            if (debug == "1"){std::cout << "Yes! \n";}
            // We call this function to judge Q-s of this C and create R-s and R-components based on them
            createDetPart(pvwaa, ci, C[ci], C[ci], R, isqmay, isqmust, sdba, Rname, phi1, phi2, debug);
        }
    }

    if (debug == "1") { std::cout << "ND part edge acceptation correction. "; }
    for (unsigned ci = 0; ci < nc; ++ci) {
        for (auto& t: sdba->out(ci))
        {
            for (unsigned d: pvwaa->univ_dests(t.dst)) {
                if (debug == "1") {
                    std::cout << "\nEdge " << t.src << "-" << d << " accepting labels: " << t.acc << ". ";
                }
                if (t.acc == 2) {
                    t.acc = 0;
                    if (debug == "1") { std::cout << "We set acc to " << t.acc << ". "; }
                }
            }
        }
    }

    if (debug == "1") { std::cout << "\n\n"; }

    // Call spot's merge edges function
    sdba->merge_edges();

    return sdba;
}

bool checkMayReachableStates(std::shared_ptr<spot::twa_graph> vwaa, std::set<std::string> Conf,
                             std::set<std::string> Valid, bool isqmay[]){

    // We check each state whether it is Qmay. If it is, we add it to Valid with all successors
    for (auto q : Conf)
    {
        if (q.empty() || !isdigit(q.at(0))){
            if (q != "{}") {
                std::cout << "We are in BADSTATE: " << q << ". "; // todo Better error message
            }
            else {
                // This state is {} and hence is Qmust // todo Is this right?
            }
        } else {
            if (isqmay[std::stoi(q)]) {
                addToValid(vwaa, q, Valid);
            }
        }
    }

    // We check and return whether all states in Conf are valid (QMays and their successors)
    for (auto q : Conf)
    {
        if (!(Valid.find(q) != Valid.end())){
            return false;
        }
    }
    return true;
}

void addToValid(std::shared_ptr<spot::twa_graph> vwaa, std::string q, std::set<std::string> &Valid){
    Valid.insert(q);
    // We add into Valid all states reachable from q too
    for (auto &t: vwaa->out((unsigned int)std::stoi(q))) {
        for (unsigned d: vwaa->univ_dests(t.dst)) {
            // We exclude loops for effectivity, as they never need to be checked to be added again
            if (std::to_string(d) != q) {
                addToValid(vwaa, std::to_string(d), Valid);
            }
        }
    }
}

void createDetPart(std::shared_ptr<spot::twa_graph> vwaa, unsigned ci, std::set<std::string> Conf,
                   std::set<std::string> remaining, std::set<std::string> R, bool isqmay[], bool isqmust[],
                   spot::twa_graph_ptr &sdba, std::map<unsigned, std::set<std::string>> &Rname,
                   std::map<unsigned, std::set<unsigned>> &phi1, std::map<unsigned, std::set<unsigned>> &phi2,
                   std::string debug){

    // We choose first q that comes into way
    auto it = remaining.begin();
    std::string q;
    if (it != remaining.end()) q = *it;

    if (debug == "1"){std::cout << "\nFunction createDetPart\nWe chose q: " << q << ". ";}
    // Erase it from remaining as we are checking it now
    remaining.erase(q);

    // Checking state correctness
    if (q.empty() || !isdigit(q.at(0))){
        if (q != "{}") {
            std::cout << "We are in BADSTATE: " << q << ". "; // todo Better error message
        }
        else {
            //If the state is {}, we know it is Qmust.
            if (debug == "1"){std::cout << "q is {} (which is Qmust), adding to R. ";}
            if (R.count(q) == 0) {
                R.insert(q);
            }
        }
    } else {
        // If this state is Qmust, we add it (and don't have to check Qmay)
        if (isqmust[std::stoi(q)]){
            if (debug == "1"){std::cout << "It is Qmust, adding to R. ";}
            if (R.count(q) == 0) {
                R.insert(q);
            }
        } else {
            // If it is Qmay, we recursively call the function and try both adding it and not
            if (isqmay[std::stoi(q)]){
                if (debug == "1"){std::cout << "It is Qmay (and not Qmust!), adding to R";}

                // We create a new branch with new R and add the state q to this R
                std::set<std::string> Rx = R;
                if (Rx.count(q) == 0) {
                    Rx.insert(q);
                }

                if (!remaining.empty()){
                    // We run the branch that builds the R where this state is added
                    if (debug == "1"){std::cout << " and creating branch including: " << q << ".\n";}
                    createDetPart(vwaa, ci, Conf, remaining, Rx, isqmay, isqmust, sdba, Rname, phi1, phi2, debug);
                } else{
                    // If this was the last state, we have one R complete. Let's build an R-component from it.
                    if (debug == "1"){std::cout << " and this was lastx state!\n----------> \nCreate Rx comp: \n";}
                    createRComp(vwaa, ci, Conf, Rx, sdba, Rname, phi1, phi2, debug);
                    if (debug == "1"){std::cout << " \n<---------- \n";}
                }
                // We also continue this run without adding this state to R - representing the second branch
                if (debug == "1"){std::cout<< "Also continuing for not adding q to R - ";}
            }
        }
        if (debug == "1"){std::cout << "Done checking for q: " << q;}

    }
    if (debug == "1"){std::cout << "\n Is this last state? ";}
    // If this was the last state, we have this R complete. Let's build an R-component from it.
    if (remaining.empty()){
        if (debug == "1"){std::cout << " YES!  \n----------> \nCreate R comp: \n";}
        createRComp(vwaa, ci, Conf, R, sdba, Rname, phi1, phi2, debug);
        if (debug == "1"){std::cout << " \n<---------- \n";}
    } else{
        if (debug == "1"){std::cout << " NO! Check another: \n";}
        createDetPart(vwaa, ci, Conf, remaining, R, isqmay, isqmust, sdba, Rname, phi1, phi2, debug);
    }

    return;
}

void createRComp(std::shared_ptr<spot::twa_graph> vwaa, unsigned ci, std::set<std::string> Conf,
                 std::set<std::string> R, spot::twa_graph_ptr &sdba, std::map<unsigned, std::set<std::string>> &Rname,
                 std::map<unsigned, std::set<unsigned>> &phi1, std::map<unsigned, std::set<unsigned>> &phi2,
                 std::string debug){
    if (debug == "1"){
        std::cout << "\nFunction createRComp\nStates of Conf: ";
        for (auto x : Conf){
            std::cout << x << ", ";
        }
        std::cout << " States of R: ";
        for (auto y : R){
            std::cout << y << ", ";
        }
        std::cout << " Num of states of sdba: " << sdba->num_states();
        std::cout << " Go:\n";
    }

    // todo optimalization, if R is empty?

    // Note: "vwaa->num_states()-1" is the last state of the vwaa, which is always the TT state.

    // The phis of this state
    std::set<unsigned> p1;
    std::set<unsigned> p2;

    // First we construct the edges from C into the R component by getting the correct phi1 and phi2
    unsigned nq = vwaa->num_states();
    const spot::bdd_dict_ptr dict = sdba->get_dict();

    // For each edge label ("a,b,c", "a,b,!c", "a,!b,c"...) of the alphabet
    for (auto label : gAlphabet){
        for (unsigned q = 0; q < nq; ++q) {
            if (debug == "1") { std::cout << "\nFor label: " << label << ", checking q: " << q << ". "; }
            // To deal with phi1, q either needs to not be in R, or see below *
            if (R.find(std::to_string(q)) == R.end()) {
                if (debug == "1") { std::cout << "q is not in R. \n"; }
                // q has to be in Conf to deal with phi1
                if (Conf.find(std::to_string(q)) != Conf.end()){
                    if (debug == "1") { std::cout << "q is in Conf\n"; }
                    for (auto &t: vwaa->out(q)) {
                        for (unsigned tdst: vwaa->univ_dests(t.dst)) {
                            if (debug == "1") { std::cout << "E " << t.src << "-" << tdst << " t.cond: " << t.cond
                                                          << " label: " << label << ". \n"; }
                            if (bdd_implies(label, t.cond)) {
                            //if (gExact || t.cond == bdd_true()) {
                                if (debug == "1") { std::cout << "This label is the same as label: " << label << ". "; }
                                // Replace the edges ending in R with TT
                                if (R.find(std::to_string(tdst)) == R.end()) { // If tdst was in R, we'd add TT
                                    if (debug == "1") {
                                        std::cout << "t.dst is not in R - adding " << tdst << " to phi1\n";
                                    }
                                    p1.insert(tdst);
                                }
                            }
                        }
                    }
                }
            } else { // * or q must be in Conf && edge must not be accepting
                if (debug == "1") { std::cout << "q is in R. \n"; }
                for (auto &t: vwaa->out(q)) {
                    for (unsigned tdst: vwaa->univ_dests(t.dst)) {
                        if (debug == "1") { std::cout << "E " << t.src << "-" << tdst << " t.cond:" << t.cond
                                                      << " label: " << label << ". \n"; }
                        // If t.cond contains this label as one of the conjunctions
                        if (bdd_implies(label, t.cond)) {
                            if (debug == "1") { std::cout << "This label is the same as label: " << label << ". "; }
                            if ((Conf.find(std::to_string(q)) != Conf.end()) && t.acc == 0) {  // this is a correct mod. tr.
                                if (debug == "1") { std::cout << "q is in Conf and e is not acc. \n"; }
                                // Replace the edges ending in R with TT
                                if (R.find(std::to_string(tdst)) == R.end()) { // If tdst was in R, we'd add TT
                                    if (debug == "1") {
                                        std::cout << "t.dst is not in R - adding " << tdst << " to phi1\n";
                                    }
                                    p1.insert(tdst);
                                }
                            }
                        }
                    }
                }
                if (debug == "1") { std::cout << "Adding q to phi2. \n"; }
                // When q is in R, we always add it to phi2
                p2.insert(q);
            }
        }

        if (debug == "1") {
            std::cout << "\nThe phis we just made: phi1: ";
            for (auto x : p1){
                std::cout << x << ", ";
            }
            std::cout << "phi2: ";
            for (auto x : p2){
                std::cout << x << ", ";
            }
            std::cout << "\nAll edges of Conf before: \n";
            for (unsigned c = 0; c < sdba->num_states(); ++c) {
                for (auto i: sdba->succ(sdba->state_from_number(c))) {
                    std::cout << " Bdd of edges-label: " << i->cond() << " from " << c
                              << " to " << i->dst();
                    if (sdba->state_from_number(c) == i->dst()) { std::cout << " (loop)"; }
                    std::cout << ".\n";
                }
            }
        }

        // We need to check if this R-component state exists already
        // addedStateNum is the number of the state if it exists, else value remains as a "new state" number:
        unsigned addedStateNum = sdba->num_states();
        if (debug == "1") { std::cout << "Checking if it exists: R: ";}

        for (unsigned c = 0; c < sdba->num_states(); ++c) {
            if (debug == "1") {
                std::cout << "\nTry c: " << c << " Rname: ";
                for (auto x : Rname[c]){
                    std::cout << x << ", ";
                }
                std::cout << "phi1: ";
                for (auto x : phi1[c]){
                    std::cout << x << ", ";
                }
                std::cout << "phi2: ";
                for (auto x : phi2[c]){
                    std::cout << x << ", ";
                }
            }
            if (Rname[c] == R && phi1[c] == p1 && phi2[c] == p2){
                addedStateNum = c;
                if (debug == "1") { std::cout << "<- this! it exists already.";}
                break;
            }
        }
        if (debug == "1") { std::cout << "\nThe statenum is: " << addedStateNum << "\n";}

        // If the state doesn't exist yet, we create it with "sdba->num_states()-1" becoming its new number.
        if (addedStateNum == sdba->num_states()) {
            sdba->new_state();         // addedStateNum is now equal to sdba->num_states()-1
            Rname[sdba->num_states() - 1] = R;
            phi1[sdba->num_states() - 1] = p1;
            phi2[sdba->num_states() - 1] = p2;
            //(*(sdba->get_named_prop(<std::vector<std::string>>("state-names")))[sdba->num_states()-1] = "New"; //todo name states?
            sdba->new_edge(ci, addedStateNum, label, {});
        } else {
            bool connected = false;
            // If the state already exists, we check if there is an edge leading there from the current state
            for (auto &t: sdba->out(ci)) {
                if (debug == "1") {
                    std::cout << "Adding new label to the edge under OR: " << t.src << "-" << t.dst
                              << " bdd:" << t.cond << " label: " << label << ". \n";
                }
                // If there is such an edge, we add this label via "OR" to the bdd
                if (t.dst == addedStateNum) {
                    connected = true;
                    t.cond = bdd_or(t.cond, label);
                }
            }
            // If there isn't such an edge, we create a new one
            if (!connected){
                sdba->new_edge(ci, addedStateNum, label, {});
            }
        }


        // We connect the state to this configuration under the currently checked label
        if (debug == "1"){std::cout << "New edge from C" << ci << " to C" << addedStateNum << " labeled " << label
                    << " (" << label << ").";}

        // If the state is new, add all successors of this state to the sdba and connect them
        if (addedStateNum == sdba->num_states()-1) {
            addRCompStateSuccs(vwaa, sdba, addedStateNum, Conf, Rname, phi1, phi2, debug);
        }


        if (debug == "1") {
            std::cout << "\nAll edges of Conf after adding successors: (back in function createRComp)\n";
            for (unsigned c = 0; c < sdba->num_states(); ++c) {
                for (auto i: sdba->succ(sdba->state_from_number(c))) {
                    std::cout << " t.cond: " << i->cond() << " from " << c << " to " << i->dst();
                    if (sdba->state_from_number(c) == i->dst()) { std::cout << " (loop)"; }
                    std::cout << ".\n";
                }
            }
            std::cout << "\nlaststatenum:" << sdba->num_states()-1 << ", phi1: ";
            for (auto x : phi1[sdba->num_states()-1]){
                std::cout << x << ", ";
            }
            std::cout << "phi2: ";
            for (auto x : phi2[sdba->num_states()-1]){
                std::cout << x << ", ";
            }
            std::cout << "\nEnd of run of function createRComp for this label.\n";
        }
    }
}


// Adds successors of state statenum (and their successors, recursively)
void addRCompStateSuccs(std::shared_ptr<spot::twa_graph> vwaa, spot::twa_graph_ptr &sdba, unsigned statenum,
                        std::set<std::string> Conf, std::map<unsigned, std::set<std::string>> &Rname,
                        std::map<unsigned, std::set<unsigned>> &phi1, std::map<unsigned, std::set<unsigned>> &phi2,
                        std::string debug){

    if (debug == "1"){std::cout << "\n\n>>>>>>  Function addRCompStateSuccs for state " << statenum;}

    // The R and phis of the state we are adding successors of
    std::set<std::string> R = Rname[statenum];
    std::set<unsigned> p1 = phi1[statenum];
    std::set<unsigned> p2 = phi2[statenum];

    // The phis for the successor state (will reset for each added state)
    std::set<unsigned> succp1;
    std::set<unsigned> succp2;

    const spot::bdd_dict_ptr dict = sdba->get_dict();

    // For each edge label of the alphabet we compute phis of the reached state (succp1 and succp2)
    for (auto label : gAlphabet) {

        succp1.clear();
        succp2.clear();

        if (debug == "1") { if (debug == "1") { std::cout << "\nWe check label: " << label; }
        }

        if (debug == "1") { std::cout << "\nFor all states of p1: "; }
        // Go through all states q of p1. For each, if edge under label is a correct m.t., add its follower to succp1
        for (auto q : p1){
            if (debug == "1") { std::cout << "\nChecking q: " << q << ". "; }
            // To deal with phi1, q either needs to not be in R, or see below *
            if ((R.find(std::to_string(q)) == R.end())) {
                if (debug == "1") { std::cout << "It's not in R. \n"; }
                // Find the edge under "label"
                for (auto &t: vwaa->out(q)) {
                    for (unsigned tdst: vwaa->univ_dests(t.dst)) {
                        if (debug == "1") { std::cout << "E " << t.src << "-" << tdst << " t.cond:" << t.cond
                                                      << " label: " << label << ". \n"; }
                        // If t.cond contains this label as one of the conjunctions
                        if (bdd_implies(label, t.cond)) {
                            if (debug == "1") { std::cout << "<-the label is right. "; }
                            if (R.find(std::to_string(tdst)) == R.end()) { // If tdst was in R, we'd add TT
                                if (debug == "1") { std::cout << "adding tdst (" << tdst << ") to succphi1\n"; }
                                succp1.insert(tdst);
                            }
                        }
                    }
                }
            } else { // * or q must be in C && edge must not be accepting
                if (debug == "1") { std::cout << "It's in R. \n"; }
                if (Conf.find(std::to_string(q)) != Conf.end()) {
                    for (auto &t: vwaa->out(q)) {
                        for (unsigned tdst: vwaa->univ_dests(t.dst)) {
                            if (debug == "1") { std::cout << "E " << t.src << "-" << tdst << " t.cond:" << t.cond
                                                          << " label: " << label << ". \n"; }
                            if (t.acc == 0) {
                                // If t.cond contains this label as one of the conjunctions
                                if (bdd_implies(label, t.cond)) {
                                    if (debug == "1") { std::cout << "<- not accepting and the label is right. "; }
                                    if (R.find(std::to_string(tdst)) == R.end()) { // If tdst was in R, we'd add TT
                                        if (debug == "1") {
                                            std::cout << "adding tdst (" << tdst << ") to succphi1\n";
                                        }
                                        succp1.insert(tdst);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        if (debug == "1") { std::cout << "\nFor all states of p2: "; }
        // Go through all states q of p2. For each, if edge under label is correct m.t., add its follower to succp2
        for (auto q : p2){
            if (debug == "1") { std::cout << "\nChecking q: " << q << ". "; }
            // To deal with phi1, q either needs to not be in R, or see below *
            if ((R.find(std::to_string(q)) == R.end())) {
                if (debug == "1") { std::cout << "It's not in R. \n"; }
                // Find the edge under "label"
                for (auto &t: vwaa->out(q)) {
                    for (unsigned tdst: vwaa->univ_dests(t.dst)) {
                        if (debug == "1") { std::cout << "E " << t.src << "-" << tdst << " t.cond:" << t.cond
                                                      << " label: " << label << ". \n"; }
                        // If t.cond contains this label as one of the conjunctions
                        if (bdd_implies(label, t.cond)) {
                            if (debug == "1") { std::cout << " added tdst (" << tdst << ") to succphi2. \n"; }
                            succp2.insert(tdst);
                        }
                    }
                }
            } else { // * or q must be in C && edge must not be accepting
                if (debug == "1") { std::cout << "It's in R. \n"; }
                if (Conf.find(std::to_string(q)) != Conf.end()) {
                    for (auto &t: vwaa->out(q)) {
                        for (unsigned tdst: vwaa->univ_dests(t.dst)) {
                            if (debug == "1") { std::cout << "E " << t.src << "-" << tdst << " t.cond:" << t.cond
                                                          << " label: " << label << ". \n"; }
                            if (t.acc == 0) {
                                if (debug == "1") { std::cout << "q is in Conf and e is not acc. Tcond " << t.cond
                                                              << "(the label we check), bddlabel we are looking for: "
                                                                 << label << ".\n";}
                                // If t.cond contains this label as one of the conjunctions
                                if (bdd_implies(label, t.cond)) {
                                    if (debug == "1") { std::cout << " added tdst (" << tdst << ")  to succphi2. \n"; }
                                    succp2.insert(tdst);
                                }
                            }
                        }
                    }
                }
            }
        }

        if (debug == "1") { std::cout << " Done foralling. \n"; }
        bool accepting = false;

        if (succp1.empty()) {
            // We make this the breakpoint and change succp1 and succp2 completely
            if (debug == "1") { std::cout << "Succphi1 is empty, changing succp1 and 2 a lot\n"; }
            for (auto q : succp2) {
                if (R.find(std::to_string(q)) == R.end()) { // If q was in R, we'd add TT
                    if (debug == "1") { std::cout << "Adding q: " << q << " to succphi1\n"; }
                    succp1.insert(q);
                }
            }
            succp2.clear();
            for (auto q : R) {
                succp2.insert((unsigned int) (std::stoi(q)));
            }
            accepting = true;

            if (debug == "1") {
                std::cout << "New values: succphi1: ";
                for (auto x : succp1) {
                    std::cout << x << ", ";
                }
                std::cout << "succphi2: ";
                for (auto x : succp2) {
                    std::cout << x << ", ";
                }
            }
        }

        // We need to check if this R-component state exists already
        // succStateNum is the number of the state if it exists, else value remains as a "new state" number:
        unsigned succStateNum = sdba->num_states();
        if (debug == "1") { std::cout << "Succstatenum = sdbanumstates: " << succStateNum; }
        bool existsAlready = false;

        for (unsigned c = 0; c < sdba->num_states(); ++c) {
            if (debug == "1") {
                std::cout << "\nTry c: " << c << " Rname: ";
                for (auto x : Rname[c]) {
                    std::cout << x << ", ";
                }
                std::cout << "phi1: ";
                for (auto x : phi1[c]) {
                    std::cout << x << ", ";
                }
                std::cout << "phi2: ";
                for (auto x : phi2[c]) {
                    std::cout << x << ", ";
                }
            }
            if (Rname[c] == R && phi1[c] == succp1 && phi2[c] == succp2) {
                succStateNum = c;
                existsAlready = true;
                if (debug == "1") { std::cout << " < this!\n"; }
                break;
            }
        }
        if (debug == "1") { std::cout << "\nSuccstatenum: " << succStateNum << "\n"; }

        // If the state doesn't exist yet, we create it with "sdba->num_states()-1" becoming its new number.
        if (succStateNum == sdba->num_states()) {   // the same as "if !existsAlready"
            if (debug == "1") { std::cout << " Making new state\n"; }
            sdba->new_state();         // succStateNum is now equal to sdba->num_states()-1
            Rname[succStateNum] = R;
            phi1[succStateNum] = succp1;
            phi2[succStateNum] = succp2;
            if (debug == "1") { std::cout << "Newly added state num: " << succStateNum << ", R: ";
                for (auto x : R){
                    std::cout << x << ", ";
                }
                std::cout << "succp1: ";
                for (auto x : succp1) {
                    std::cout << x << ", ";
                }
                std::cout << "succp2: ";
                for (auto x : succp2) {
                    std::cout << x << ", ";
                }
                std::cout << " sdba num states: " << sdba->num_states() << "\n";
            }
            // (*(sdba->get_named_prop<std::vector<std::string>>("state-names")))[sdba->num_states()-1] = "New"; todo name states?
            if (accepting) {
                sdba->new_edge(statenum, succStateNum, label, {0});
            } else {
                sdba->new_edge(statenum, succStateNum, label, {});
            }
         } else {
            bool connected = false;
            // If the state already exists, we check if there is a same-acc edge leading there from the current state
            for (auto &t: sdba->out(statenum)) {
                // If there is such an edge, we add it as OR to the existing edge instead of creating a new edge
                if (t.dst == succStateNum && (((t.acc != 0 && accepting) || (t.acc == 0 && !accepting)))){
                    if (debug == "1") { std::cout << "Adding new label to the edge under OR: " << t.src << "-" << t.dst
                              << " bdd:" << t.cond << " bddithvarlabel" << label << ". \n"; }
                    connected = true;
                    t.cond = bdd_or(t.cond, label);
                }
            }
            // If there isn't such an edge, we create a new one
            if (!connected){
                if (accepting) {
                    sdba->new_edge(statenum, succStateNum, label, {0});
                } else {
                    sdba->new_edge(statenum, succStateNum, label, {});
                }
            }
        }

        // If the state is new, add all further successors of this successor to the sdba and connect them
        if (!existsAlready) {
            if (sdba->num_states() < 8) { // todo remove limit of states!
                addRCompStateSuccs(vwaa, sdba, succStateNum, Conf, Rname, phi1, phi2, debug);
            }
        }

    }
    if (debug == "1") { std::cout << "\n<<<<<<   End of function addRCompStateSuccs of state " << statenum << "\n"; }
}





// BDD notes:

// to find out whether label is positive somewhere in BDD, like whether {a} is in {b | (a & !c)}
// the allsathandler
/*
unsigned gLabel;
bool gContains;
void allSatContainsHandler(char* varset, int size) {
    gContains = false;
    if (varset[gLabel] == 1){
        gContains = true;
    }
}
// and these lines:
gLabel = q;
bdd_allsat(t.cond, allSatContainsHandler); // browse t.cond to see if there is gLabel : 1. updates gContains
if (gContains || t.cond == bdd_true()){
    std::cout << "\n Yes! " << gLabel << " is in this t.cond";
}*/

// to find out whether label is in BDD separated as OR. like whether {a} is in {(b&c) | a}
// the allsathandler
/*
unsigned gLabel;
bool gExact = false;
void allSatExactHandler(char* varset, int size) {
    if (!gExact) {
        if (varset[gLabel] == 1) {
            gExact = true;
            for (int v = 0; v < size; ++v) {
                if (varset[v] == 1) {
                    if (v != gLabel) {
                        gExact = false;
                    }
                }
            }
        }
    }
}
// and these lines:
gLabel = label;
gExact = false;
bdd_allsat(t.cond, allSatExactHandler); // browse t.cond to see if it is "x OR glabel". updates gExact
if (gExact || x == bdd_true()) {
    std::cout << "\n Yes! " << gLabel << " is in this t.cond";
}
 */
/*
    bdd a = bdd_ithvar(0);
    bdd b = bdd_ithvar(1);
    bdd c = bdd_ithvar(2);
    bdd dqw = bdd_ithvar(3);
    bdd e = bdd_ithvar(4);

    std::cout << ", a " << a;
    std::cout << ", b " << b;
    std::cout << ", !b " << !b;
    std::cout << ", c " << c;
    std::cout << ", d " << d;
    std::cout << ", e " << e;
    std::cout << ", !e " << !e;
    std::cout << "\na and b and c and d and e " << bdd_and(a, bdd_and(b, bdd_and(c, bdd_and(d, e))));
    std::cout << "\na or b or c or d or e " << bdd_or(a, bdd_or(b, bdd_or(c, bdd_or(d, e))));

    bdd x = bdd_or(a, bdd_and(b, bdd_and(!c, bdd_or(d, !b))));
    std::cout << "\na or (b and (!c and (d or !b))) = x: " << x;

    bdd x = bdd_or(c, bdd_and(b, bdd_and(!a, bdd_or(d, bdd_or(!b, bdd_or(!c, a))))));

    std::cout << "\nc or (b and (!a and (d or !b))) = x: " << x << "\n";

    for (unsigned label = 0; label < 2; ++label) {
        std::cout << "\n\nlabel " << label << " as bdd: " << bdd_ithvar(label);
        for (unsigned q = 0; q < nq; ++q) {
            for (auto &t: pvwaa->out(q)) {
                for (unsigned d: pvwaa->univ_dests(t.dst)) {
                    std::cout << "\nedge from " << q << " to " << t.dst;
                    // checking if this edge is edge under label a
                    std::cout << "\ncond " << t.cond;
                    // find if label a is in t.cond
                    gLabel = q;
                    bdd_allsat(t.cond, allSatExactHandler); // browse t.cond to see if there is gLabel : 1. updates contains
                    if (gExact || t.cond == bdd_true()){
                        std::cout << "\n Yes! " << gLabel << " is in this t.cond";
                    }
                }
            }
        }
    }*/

/* Check if input contains a varset = gBdd
bdd gBdd;
bool gExact = false;
void allSatExactBddHandler(char* varset, int size) {
    std::cout << "working for varset:" << varset << "\n";
    // Check if the gBdd is this varset of input
    if (!gExact) {
        bdd varsetbdd = bdd_true();
        bdd newinner = bdd_true();
        for (int v = 0; v < size; ++v) {
            std::cout << "v: " << v << ", varset[v]: " << varset[v] << "\n";
            if (varset[v] == 1) {
                std::cout << "its1";
                newinner = bdd_and(varsetbdd, bdd_ithvar(v));
                varsetbdd = newinner;
            }
            if (varset[v] == 0){
                std::cout << "its0";
                newinner = bdd_and(varsetbdd, bdd_not(bdd_ithvar(v)));
                varsetbdd = newinner;
            }
        }
        std::cout << "varset after parsing " << varsetbdd << " gbdd: " << gBdd << "\n";
        if (gBdd == varsetbdd){
            std::cout << "yesesyesey: gbdd " << gBdd << " varsetbdd" << varsetbdd << "\n";
            gExact = true;
        }
    }
}*/

/*
// Finds out whether any OR expression of varset (input) is in gBdd
void allSatTwoORSetHandler(char* varset, int size) {
    std::cout << "go, size: " << size << "\n";
    // For each OR expression, create a separate bdd "thisVarsetbdd"
    bdd outerVarsetbdd = bdd_true();
    bdd newouter = bdd_true();
    for (int v = 0; v < size; ++v) {
        std::cout << " V: " << v << ", bdd ithvar: " << bdd_ithvar(v) << ", varset[v] " << varset[v] << " out " << outerVarsetbdd << "\n";
        if (varset[v] == 1) {
            std::cout << "v1111";
            newouter = bdd_and(outerVarsetbdd, bdd_ithvar(v));
            outerVarsetbdd = newouter;
        }
        if (varset[v] == 0){
            std::cout << "v2222";
            outerVarsetbdd = bdd_and(outerVarsetbdd, bdd_not(bdd_ithvar(v)));
            outerVarsetbdd = newouter;
        }
    }
    // Check if thisVarsetbdd is an OR subexpression of gBdd
    gORSet = outerVarsetbdd;
    std::cout << "all ok for outerVarsetbdd " << outerVarsetbdd << "\n";
    bdd_allsat(bdd_ithvar(0), allSatExactBddHandler);
    std::cout << "finished for outerVarsetbdd " << outerVarsetbdd << "\n";
}*/


// Finds out whether gLabel is a part of the varset as one of OR-expressions, returns in gExact
/*int gLabel;
void allSatExactHandler(char* varset, int size) {
    if (!gExact) {
        if (varset[gLabel] == 1) {
            gExact = true;
            for (int v = 0; v < size; ++v) {
                if (varset[v] == 1) {
                    if (v != gLabel) {
                        gExact = false;
                    }
                }
            }
        }
    }
}*/

/* Adds varsets into gAlphabet
std::vector<bdd> gAlphabet;
void allSatAlphabetHandler(char* varset, int size) {
    bdd thisVarsetbdd = bdd_true();
    for (int v = 0; v < size; ++v) {
        if (varset[v] == 1) {
            thisVarsetbdd = bdd_and(thisVarsetbdd, bdd_ithvar(v));
        }
        if (varset[v] == 0){
            thisVarsetbdd = bdd_and(thisVarsetbdd, bdd_not(bdd_ithvar(v)));
        }
    }
    bool wasThere = false;
    for (auto i = gAlphabet.begin(); i != gAlphabet.end(); i++)
        if (*i == thisVarsetbdd)
            wasThere = true;
    if (!wasThere)
        gAlphabet.push_back(thisVarsetbdd);
}*/