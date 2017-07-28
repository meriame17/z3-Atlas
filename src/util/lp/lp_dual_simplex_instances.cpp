/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#include "util/lp/lp_dual_simplex.hpp"
template lp::mpq lp::lp_dual_simplex<lp::mpq, lp::mpq>::get_current_cost() const;
template void lp::lp_dual_simplex<lp::mpq, lp::mpq>::find_maximal_solution();
template double lp::lp_dual_simplex<double, double>::get_current_cost() const;
template void lp::lp_dual_simplex<double, double>::find_maximal_solution();
