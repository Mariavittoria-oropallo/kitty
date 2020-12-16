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
  G , L, E
};
/* >=      <=  == */

struct Constraint {
  std::vector<int64_t> weights;
  Constraint_Type type;
  int constant; /* the right-hand side constant */
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
  \param plf Pointer to a vector that will hold a linear form of `tt` if it is a TF.
             The linear form has `tt.num_vars()` weight values and the threshold value
             in the end.
  \return `true` if `tt` is a TF; `false` if `tt` is a non-TF.
*/
template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool is_threshold(TT& tt, std::vector<int64_t>* plf = nullptr )
{
  std::vector<int64_t> linear_form;
  bool is_less = false;
  bool is_higher = false;

  uint64_t num_var = tt.num_vars();
  uint64_t num_bit = tt.num_bits();


  /* Check if tt is negative unate or binate */

  for (uint64_t var=0u; var<num_var; var++){

    auto const tt0 = cofactor0( tt, var);
    auto const tt1 = cofactor1( tt, var);

    for(uint64_t j=0u; j<num_bit; j++){
      if (get_bit(tt1, j) >  get_bit(tt0, j))
        is_higher = true;

      if (get_bit(tt1, j) <  get_bit(tt0, j))
        is_less = true;
    }

    /*Change f into f_star*/
    if( !is_higher && is_less ){
      flip_inplace(tt, var);
    }

    if( is_higher && is_less )    /* TT IS BINATE  */
      return false;

    is_higher = false;
    is_less = false;

  }

  /* ONSET anf OFFSET*/
  auto cube_ONSET = get_prime_implicants_morreale(tt);
  auto tt_neg = unary_not(tt);
  auto cube_OFFSET = get_prime_implicants_morreale(tt_neg);

  /*The Constraints*/
  std::vector<Constraint> constraints;

  for (auto& i : cube_ONSET){
    Constraint constraint;
    for(uint64_t var = 0; var < num_var; var++){
      if (i.get_mask(var) == 1){
        if(i.get_bit(var) == 1){
          constraint.weights.emplace_back(1);
        }
        else{
          constraint.weights.emplace_back(0);
        }
      }
      else{
        constraint.weights.emplace_back(0);
      }
    }
    constraint.weights.emplace_back(-1);
    constraint.type = G;
    constraint.constant = 0;
    constraints.emplace_back(constraint);
  }

  for (auto& i : cube_OFFSET){
    Constraint constraint;
    for(uint64_t var = 0; var < num_var; var++){
      if (i.get_mask(var) == 0){
        constraint.weights.emplace_back(1);
      }
      else{
        constraint.weights.emplace_back(0);
      }
    }
    constraint.weights.emplace_back(-1);
    constraint.type = L;
    constraint.constant = -1;
    constraints.emplace_back(constraint);
  }


  /*Positive weights*/
  for(uint64_t var = 0; var <= num_var; var++){
    Constraint constraint;
    for(uint64_t i = 0; i <= num_var; i++){
      constraint.weights.emplace_back(0);
    }
   // constraint.variables.emplace_back(var);
    constraint.weights[var] = 1;
    constraint.constant = 0;
    constraint.type = G;
    constraints.emplace_back(constraint);
  }


  /*LP*/

  lprec *lp;
  auto num_rows = constraints.size();
  std::vector<double> row;

  /* Create a new LP model */
  lp = make_lp(0, num_var+1);
  if(lp == nullptr) {
    fprintf(stderr, "Unable to create new LP model\n");
    return(false);
  }

  set_add_rowmode(lp, TRUE);

  /*the objective function*/
  row.emplace_back(1.0);
  for(uint64_t col = 1; col<=num_var+1; col++){
    row.emplace_back(1.0);
  }

  set_obj_fn(lp, row.data());

  for(uint64_t rows = 0; rows < num_rows; rows++){
    for(uint64_t col = 1; col <= num_var+1; col++){
      row[col] = constraints[rows].weights[col-1];
    }
    if(constraints[rows].type == G )
      add_constraint(lp, row.data(), GE, constraints[rows].constant);
    else if (constraints[rows].type == L)
      add_constraint(lp, row.data(), LE, constraints[rows].constant);
  }

  set_add_rowmode(lp, FALSE);
  set_minim(lp);
  print_lp(lp);
  set_verbose(lp, IMPORTANT);

  for(auto i = 1u; i< num_var+1; i++){
    set_int(lp, i, TRUE);
  }

  int ret = solve(lp);
  if(ret == OPTIMAL){    //tt is TF
    /* objective value */
    printf("Objective value: %f\n", get_objective(lp));

    /* variable values */
    get_variables(lp, row.data());
    for(uint64_t i = 0; i < num_var+1; i++){
      /* push the weight and threshold values into `linear_form` */
      linear_form.push_back((int)(row[i]));
    }

    /*print values*/
    for(uint64_t j = 0; j <= num_var +1; j++){
      printf( "%s: %f\n", get_col_name( lp, j + 1 ), row[j] );
    }
  }
  else
    return false;

  if ( plf ){
    *plf = linear_form;
  }
  return true;
}


} /* namespace kitty */
