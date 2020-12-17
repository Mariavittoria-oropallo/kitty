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
#include "implicant.hpp"
#include "cube.hpp"


enum Constraint_Type {
  G , L
};
/* >=   <=  */

struct Constraint {
  std::vector<int64_t> weights;
  Constraint_Type type;
};


namespace kitty
{

/*! \brief Threshold logic function identification

  Given a truth table, this function determines whether it is a threshold logic function (TF)
  and finds a linear form if it is. A Boolean function is a TF if it can be expressed as

  f(x_1, ..., x_n) = \sum_{i=1}^n w_i x_i >= T

  where w_i are the weight values and T is the threshold value.
  The linear form of a TF is the vector [w_1, ..., w_n; T].

  \param tt_fstar The truth table
  \param plf Pointer to a vector that will hold a linear form of `f` if it is a TF.
             The linear form has `f.num_vars()` weight values and the threshold value
             in the end.
  \return `true` if `f` is a TF; `false` if `f` is a non-TF.
*/
template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool is_threshold(const TT& tt, std::vector<int64_t>* plf = nullptr )
{
  TT f = tt;  /* copy tt into f*/

  std::vector<int64_t> linear_form;

  uint64_t num_var = f.num_vars();

  std::vector<bool> neg_variables(num_var, false);

  /* Check if f is negative unate or binate */

  for (uint64_t var=0u; var<num_var; var++){

    auto const tt0 = cofactor0( f, var);
    auto const tt1 = cofactor1( f, var);

    if (implies(tt1, tt0)){    //NEGATIVE UNATE
      flip_inplace( f, var);   //Change f into f_star
      neg_variables[var] = true;   //Keep track of changed variables
    }

    else if(implies(tt0, tt1)) //POSITIVE UNATE
      continue;

    else                       //BINATE
      return false;
  }


  /* ONSET anf OFFSET*/
  auto onset_cubes = get_prime_implicants_morreale( f );
  auto offset_cubes = get_prime_implicants_morreale(unary_not(f));

  /*The Constraints*/
  std::vector<Constraint> constraints;

  /*All weights have to be positive*/
  for(uint64_t var = 0; var <= num_var; var++){
    Constraint pos_w;
    for(uint64_t i = 0; i <= num_var; i++)
      pos_w.weights.emplace_back(0);
    pos_w.weights[var] = 1;
    pos_w.type = G;
    constraints.emplace_back(pos_w);
  }

  for (auto& i : onset_cubes ){
    Constraint constraint;
    for(uint64_t var = 0; var < num_var; var++){
      if (i.get_mask(var) == 1){
        if(i.get_bit(var) == 0){
          constraint.weights.emplace_back(0);
        }
        else{
          constraint.weights.emplace_back(1);
        }
      }
      else{
        constraint.weights.emplace_back(0);
      }
    }
    constraint.weights.emplace_back(-1);  //T weight
    constraint.type = G;
    constraints.emplace_back(constraint);
  }

  for (auto& i : offset_cubes ){
    Constraint constraint;
    for(uint64_t var = 0; var < num_var; var++){
      if (i.get_mask(var) == 0){
        constraint.weights.emplace_back(1);
      }
      else{
        constraint.weights.emplace_back(0);
      }
    }
    constraint.weights.emplace_back(-1); //T coefficient
    constraint.type = L;
    constraints.emplace_back(constraint);
  }


  /*LP*/

  lprec *lp;
  std::vector<double> row;

  /* Create a new LP model */
  lp = make_lp(0, num_var+1);
  if(lp == nullptr) {
    std::cout << "Unable to create new LP model\n";
    return(false);
  }

  set_add_rowmode(lp, TRUE);

  /*the objective function*/
  for(uint64_t col = 0; col<=num_var+1; col++){
    row.emplace_back( 1.0 );
  }

  set_obj_fn(lp, row.data());

  for(auto & constraint : constraints){
    for(uint64_t i = 1; i <= num_var+1; i++){
      row[i] = constraint.weights[i-1];
    }
    if(constraint.type == G )
      add_constraint(lp, row.data(), GE, 0);
    else if (constraint.type == L)
      add_constraint(lp, row.data(), LE, -1);
  }

  set_add_rowmode(lp, FALSE);
  set_minim(lp);
  print_lp(lp);
  set_verbose(lp, IMPORTANT);

  for(auto i = 1u; i< num_var+1; i++){
    set_int(lp, i, TRUE);
  }

  int ret = solve(lp);
  if(ret == 0){    //f is TF

    /* get variables values */
    get_variables(lp, row.data());

    /*get threshold value*/
    int64_t threshold_value = row[num_var];

    for(uint64_t i = 0; i<num_var; i++){
      linear_form.emplace_back(row[i]);
      if(neg_variables[i]){
        linear_form[i] = -row[i];
        threshold_value += linear_form[i];
      }
    }
    linear_form.emplace_back(threshold_value);

    /* objective value */
    std::cout << "Objective value: \n" << get_objective(lp);

    /*print values*/
    for(uint64_t j = 0; j <= num_var +1; j++){
      std::cout << get_col_name( lp, j + 1 ) << " " << row[j] ;
    }

  }
  else
    return false;  /*no solution to the model*/

  if ( plf ){
    *plf = linear_form;
  }

  return true;
}

} /* namespace kitty */
