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
  bool is_neg = false;

  uint64_t num_var = tt.num_vars();
  uint64_t num_bit = tt.num_bits();

 // std::vector<uint64_t> bits;
  std::vector<bool> neg_variables;

  /*
  //copy bits of tt in "bits"
  for(uint64_t i=0; i<num_bit; i++){
    if(get_bit(tt, i) == 1)
      bits.emplace_back(1);
    else if (get_bit(tt, i) == 0)
      bits.emplace_back(0);
  }
  */

  /* check if tt is negative unate or binate*/
  for (uint64_t var=0u; var<num_var; var++){
    auto const tt0 = cofactor0( tt, var);
    auto const tt1 = cofactor1( tt, var);

    for(uint64_t j=0u; j<num_bit; j++){
      if (get_bit(tt1, j) >  get_bit(tt0, j))
        is_higher = true;

      if (get_bit(tt1, j) <  get_bit(tt0, j))
        is_less = true;
    }


    if( !is_higher && is_less )
    {
      is_neg = true;

      /* evaluate f*, positive unate in variable "var" */
      std::vector<bool> marked;

      /*init vector marked*/
      for(uint64_t bit = 0; bit < num_bit; bit++){
        marked.emplace_back(false);
      }

      for(uint64_t bit = 0; bit<num_bit; bit++){
        if(!marked[bit]){
          auto bit1 = get_bit( tt, bit);
          auto bit2 = get_bit( tt, bit + (1u << var));
          //auto bit1 = bits[bit];
          //auto bit2 = bits[bit + (1u << var)];

          if(bit1 == 1)
            set_bit( tt, bit + (1u << var));   //set bit i+2^var to true
            //bits[bit + (1u << var)] = 1;

          if(bit1 == 0)
            clear_bit( tt, bit+ (1u << var));
            //bits[bit + (1u << var)] = 0;

          if(bit2 == 1)
            set_bit( tt, bit);   //set bit i+2^var to true
            //bits[bit] = 1;

          if(bit2 == 0)
            clear_bit( tt, bit);
            //bits[bit] = 0;

          marked[bit] = true;
          marked[bit + (1u << var)] = true;
        }
      }

    }


    if( is_higher && is_less )    /* TT IS BINATE  */
    {
      return false;
    }

    neg_variables.emplace_back(is_neg);

    is_higher = false;
    is_less = false;

  }


  /*constraints*/
  std::vector<bool> visited;
  std::vector<Constraint> constraints;

  /*variables*/
  for(uint64_t bit=0; bit < num_bit; bit++){
    Constraint constraint;
    for(uint64_t var = 0; var < num_var; var++){
      constraint.variables.emplace_back(var);

      if( get_bit( tt, bit) == 1){
      //if( bits[bit] == 1){
        constraint.type = G;
        constraint.constant = 0;
      }
     else if(get_bit( tt, bit) == 0){
     // else if(bits[bit] == 0){
        constraint.type = L;
        constraint.constant = -1.0;
      }
    }
    constraint.variables.emplace_back(num_var);
    constraints.emplace_back(constraint);

  }

  /*coefficients*/
  for(uint64_t var = 0; var < num_var; var++)
  {
    uint8_t coef = 0;
    uint64_t bit = 0;
    uint64_t rep = 1u << var;  //2^var
    while ( bit < num_bit )
    {
      for (uint32_t i = 0; i < rep; i++ )
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
  for(uint64_t bit = 0; bit < num_bit; bit++){
    constraints[bit].coefficients.emplace_back(-1);
  }

  /*Positive weights*/
  for(uint64_t var = 0; var <= num_var; var++){
    Constraint constraint;
    for(uint64_t i = 0; i <= num_var; i++){
      constraint.coefficients.emplace_back(0);
    }
    constraint.variables.emplace_back(var);
    constraint.coefficients[var] = 1;
    constraint.constant = 0;
    constraint.type = G;
    constraints.emplace_back(constraint);
  }



  //lp_solve
  lprec *lp;
  auto num_rows = constraints.size();
  REAL row[num_var+1 + 1];     /* must be 1 more than number of columns ! */

  /* Create a new LP model */
  lp = make_lp(0, num_var+1);
  if(lp == nullptr) {
    fprintf(stderr, "Unable to create new LP model\n");
    return(false);
  }

  set_add_rowmode(lp, TRUE);

  /*the objective function*/
  for(uint64_t col = 1; col<=num_var+1; col++){
    row[col] = 1.0;
  }
  set_obj_fn(lp, row);

  for(uint64_t rows = 0; rows < num_rows; rows++){
    for(uint64_t col = 1; col <= num_var+1; col++){
      row[col] = constraints[rows].coefficients[col-1];
    }
    if(constraints[rows].type == G )
      add_constraint(lp, row, GE, constraints[rows].constant);
    else if (constraints[rows].type == L)
      add_constraint(lp, row, LE, constraints[rows].constant);
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
    get_variables(lp, row);
    for(uint64_t i = 0; i < num_var+1; i++){
      //linear_form.push_back(row[i]);
      linear_form.push_back((int)(row[i]));
    }
    for(uint64_t j = 0; j <= num_var +1; j++)
    {
      printf( "%s: %f\n", get_col_name( lp, j + 1 ), row[j] );
      /* push the weight and threshold values into `linear_form` */
    }

  }
  else
    return false;


    if ( plf )
  {
    *plf = linear_form;
  }
  return true;
}


} /* namespace kitty */
