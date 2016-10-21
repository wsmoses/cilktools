/**
 * Copyright (c) 2015 MIT License by 6.172 Staff
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to
 * deal in the Software without restriction, including without limitation the
 * rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
 * sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
 * IN THE SOFTWARE.
 **/

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <sys/time.h>
#include <sys/resource.h>
#include <cilk/cilk.h>
#include "fasttime.h"
#include <cilk/reducer_opadd.h>

#pragma GCC diagnostic ignored "-Wunused-value"
#pragma GCC diagnostic ignored "-Wunused-function"

/* int sum = 0; */

// compute the dot product of two vectors.
int dot_product(int *v, int *u, size_t n) {
  
  /* CILK_C_REDUCER_OPADD(r,int,0); */
  /* CILK_C_REGISTER_REDUCER(r); */
  int sum = 0;
  cilk_for (size_t i = 0; i < n; i++) {
    sum += v[i] * u[i];
    /* REDUCER_VIEW(r) += v[i]*u[i]; */
  }
  /* sum = REDUCER_VIEW(r); */
  /* CILK_C_UNREGISTER_REDUCER(r); */
  return sum;
}

// compute matrix * vector
void multiply_matrix_vector(int *matrix, int *vector, int *output, size_t n) {
  for (size_t i = 0; i < n; i++) {
    output[i] = dot_product(&matrix[i*n], vector, n);
  }
}

int main(int argc, char **argv) {
  // Create create a random matrix
  unsigned int seed = 42;
  size_t n = 10;
  int *matrix = (int *) malloc(sizeof(int) * n * n);
  int *vector = (int *) malloc(sizeof(int) * n);
  int *output = (int *) malloc(sizeof(int) * n);

  if (matrix == NULL || vector == NULL || output == NULL) {
    fprintf(stderr, "Failed to allocate enough memory\n");
    return 1;
  }

  for (size_t i = 0; i < n*n; i++) {
    matrix[i] = rand_r(&seed);
  }

  for (size_t i = 0; i < n; i++) {
    vector[i] = rand_r(&seed);
  }

  fasttime_t time1 = gettime();
  multiply_matrix_vector(matrix, vector, output, n);
  fasttime_t time2 = gettime();

  printf("Runtime: %lf seconds \n", tdiff(time1, time2));

  // This sum allows you to verify that your changes don't affect the output.
  int sum = 0;
  for (size_t i = 0; i < n; i++) {
    sum += output[i];
  }
  printf("Sum of entries is %d\n", sum);
  return 0;
}
