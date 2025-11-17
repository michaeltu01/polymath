#lang forge 

// The -O forces an override (regardless of what's in the .frg file)
// racket basic.frg -O run_sterling serve
option run_sterling serve
option sterling_port 10000
abstract sig Color {}
one sig Red, Yellow, Green extends Color {}

one sig Solution {color: one Color}

sig Thing {}

option verbose 5
run {#Thing = 3}
