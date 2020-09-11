From FreeSpec Require Import Core Extraction.
From CoqFFI Require Import Interface.

Instance FreeSpec_Inject `(H : Provide ix i) : Inject i (impure ix) :=
  { inject := @request ix i _ H }.
