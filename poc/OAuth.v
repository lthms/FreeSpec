Require Import FreeSpec.Control.
Require Import FreeSpec.Interface.
Require Import FreeSpec.Program.

Module Type OAuthSpec.
  Parameters (Token:  Type)
             (ID:     Type).
End OAuthSpec.

Module OAuth (Spec:  OAuthSpec).
  Inductive OAuthInterface
  : Interface :=
  | check_token (tok:  Spec.Token)
    : OAuthInterface (option Spec.ID).

  Module DSL.
    Definition check_token
               (tok:  Spec.Token)
    : Program OAuthInterface (option Spec.ID) :=
      instr (check_token tok).
  End DSL.
End OAuth.