/* kitty: C++ truth table library
 * Copyright (C) 2017-2020  EPFL
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

/*!
  \file threshold_identification.hpp
  \brief Threshold logic function identification

  \author CS-472 2020 Fall students
*/

#pragma once

#include <vector>
#include <fstream>
#include <lpsolve/lp_lib.h> /* uncomment this line to include lp_solve */
#include "traits.hpp"
#include "operations.hpp"
#include "static_truth_table.hpp"
#include "dynamic_truth_table.hpp"
#include "bit_operations.hpp"

enum Constraint_Type {
  G , L, E
};
/* >=      <=  == */

struct Constraint {
  std::vector<uint64_t> variables;
  std::vector<int64_t> coefficients;
  Constraint_Type type;
  uint64_t constant; /* the right-hand side constant */
};

namespace kitty
{

/*! \brief Threshold logic function identification

  Given a truth table, this function determines whether it is a threshold logic function (TF)
  and finds a linear form if it is. A Boolean function is a TF if it can be expressed as

  f(x_1, ..., x_n) = \sum_{i=1}^n w_i x_i >= T

  where w_i are the weight values and T is the threshold value.
  The linear form of a TF is the vector [w_1, ..., w_n; T].

  \param tt The truth table
  \param plf Pointer to a vector that will hold a linear form of `tt` if it is a TF.
             The linear form has `tt.num_vars()` weight values and the threshold value
             in the end.
  \return `true` if `tt` is a TF; `false` if `tt` is a non-TF.
*/
template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool is_threshold( const TT& tt, std::vector<int64_t>* plf = nullptr )
{
  std::vector<int64_t> linear_form;

  bool is_less = false;
  bool is_higher = false;
  bool equal = false;
  bool is_bi = false;
  bool is_neg = false;

  auto num_var =tt.num_vars();
  auto num_bit = tt.num_bits();

  std::vector<bool> neg_variables;


  /* check if tt is negative unate or binate*/
  for (auto i=0; i<num_var; i++){
    auto const tt0 = cofactor0( tt, i);
    auto const tt1 = cofactor1( tt, i);

    for(auto j=0; j<num_bit; j++){
      if (get_bit(tt1, j) >  get_bit(tt0, j))
        is_higher = true;

      if (get_bit(tt1, j) <  get_bit(tt0, j))
        is_less = true;
    }


    if(is_higher == false && is_less == true)
    {
      is_neg = true;

      /*calc new truth table, positive unate with respect to variable i*/
      calc_new_tt(tt,i);
    }

    if(is_higher == true && is_less == true)
      is_bi = true;

    neg_variables.emplace_back(is_neg);

    is_higher = false;
    is_less = false;
    equal = false;
  }

  /* TODO */

  /* if tt is non-TF: */
  if(is_bi)
  return false;

  /*constraint*/
  std::vector<bool> visited;
  std::vector<Constraint> constraints;

  /*variables*/
  for(auto bit=0; bit< num_bit; bit++){
    Constraint constraint;
    for(auto var = 0; var < num_var; var++){
      constraint.variables.emplace_back(var);

      if( get_bit(tt, bit) == 1){
        constraint.type = G;
        constraint.constant = 0;
      }
      else if(get_bit(tt, bit) == 0){
        constraint.type = L;
        constraint.constant = 1;
      }

    }
    constraint.variables.emplace_back(var+1);

    constraints.emplace_back(constraint);

  }

  /*coefficients*/
  for(auto var = 0; var < num_var; var++)
  {
    uint8_t coef = 0;
    uint64_t bit;
    uint32_t rep = 2 ^ ( tt.get_var() );
    while ( bit < num_bit )
    {
      for ( auto i = 0; i < rep; i++ )
      {
        constraints[bit].coefficients.emplace_back( coef );
        bit++;
      }
      if (coef == 0)
        coef = 1;
      else
        coef = 0;

    }
  }

  /*T coefficient*/
  for(auto bit = 0; bit< num_bit; bit++){
    constraints[bit].coefficients.emplace_back(-1);
  }

  /*Positive weights*/
  for(auto var = 0; var <= num_var; var++){
    Constraint constraint;
    constraint.variables.emplace_back(var);
    constraint.coefficients.emplace_back(1);
    constraint.constant = 0;
    constraint.type = G;
  }



  //print_lp
  std::ofstream os("file.lp", std::ofstream::out);

  /* the objective function */
  os << "min:";
  for (auto l = 1u; l <= num_var +1; ++l) {
    os << " +" << 1 << " w" << "_" << l;
  }
  os << " ;" << std::endl;

  /* the constraints */
  for (auto const &con : constraints) {
    assert(con.variables.size() == con.coefficients.size());
    for (auto v = 0u; v < con.variables.size(); ++v) {
      auto &var = con.variables.at(v);
      auto &cof = con.coefficients.at(v);
      assert(1 <= var && var <= num_var);
      assert(1 <= var && var <= num_bit);
      if (cof == 0) { continue; }
      if (cof == 1) { os << "+"; }
      else if (cof == -1) { os << "-"; }
      os << " w" << "_" << var;
    }
    switch (con.type) {
    case G: {
      os << ">=";
      break;
    }
    case L: {
      os << "<=";
      break;
    }
    case E: {
      os << "=";
      break;
    }
    default:
      assert(false);
    }
    os << " " << con.constant << ";" << std::endl;
  }

  /* variable type declaration */
  os << "int ";
  for (auto i = 1u; i <= num_var +1; ++i) {
      os << "x" << "_" << i << ", ";
  }
  os << ";" << std::endl;


  //lp_solve
  std::system( "lp_solve scheduling.lp" );

  /* Read LP model */
  lprec *lp;
  lp = read_LP("file.lp", FULL, "test model");
  if(lp == NULL) {
    return false;
  }
    /* if tt is TF: */
  else{

    /* push the weight and threshold values into `linear_form` */
    if ( plf )
    {
      *plf = lp;
    }
    return true;
  }

}

template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
void calc_new_tt(const TT& tt, uint32_t var){

  std::vector<bool> marked;
  auto num_var =tt.num_vars();
  auto num_bit = tt.num_bits();

  /*init vector marked*/
  for(auto i = 0; i<num_bit; i++){
    marked.emplace_back(false);
  }

  for(auto i = 0; i<num_bit; i++){
    if(!marked[i]){
      auto bit1 = get_bit(tt, i);
      auto bit2 = get_bit(tt, i + 2^var);

      if(bit1 == 1)
        set_bit(tt, i + 2^var);   //set bit i+2^var to true
      if(bit1 == 0)
        clear_bit(tt, i+2^var);

      if(bit2 == 1)
        set_bit(tt, i);   //set bit i+2^var to true
      if(bit2 == 0)
        clear_bit(tt, i);

      marked[i] = true;
      marked[i+2^var] = true;
    }
  }

}


} /* namespace kitty */
