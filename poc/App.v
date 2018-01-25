Require Import Coq.Strings.String.

Require Import FreeSpec.Compose.
Require Import FreeSpec.Control.
Require Import FreeSpec.Interface.
Require Import FreeSpec.Program.
Require Import FreeSpec.WEq.

Require Import FreeSpec.PoC.Nonce.
Require Import FreeSpec.PoC.OAuth.
Require Import FreeSpec.PoC.UserDb.

Local Open Scope free_scope.
Local Open Scope free_control_scope.
Local Open Scope free_weq_scope.

Module MastodonOAuthSpec <:  OAuthSpec.
  Definition Token := string.
  Definition ID := string.
End MastodonOAuthSpec.

Module MastodonOAuth := OAuth MastodonOAuthSpec.

Definition Effects
  : Interface :=
      NonceGen string
  <+> MastodonOAuth.OAuthInterface
  <+> UserDb.Query.

Definition gen_token
  : Program Effects string :=
  liftl (liftl (Request gen_nonce)).

Definition mastodon_id_from_token
           (token:  MastodonOAuthSpec.Token)
  : Program Effects (option MastodonOAuthSpec.ID) :=
  Request (InL (InR (MastodonOAuth.check_token token))).

Definition entity_from_mastodon_id
           (id:  MastodonOAuthSpec.ID)
  : Program Effects (option Entity) :=
  liftr (user_from_email id).

Definition assign_token
           (tok:  string)
           (id:   MastodonOAuthSpec.ID)
  : Program Effects unit :=
  liftr (Request (update (fun ent
                        => email (val ent) ?= id)
                       (fun user
                        => {| email := email user
                            ; token := Some tok
                            ; name := name user
                           |})
               )
        ).

Definition login
           (token:  MastodonOAuthSpec.Token)
  : Program Effects (option string) :=
  mid <- mastodon_id_from_token token                                ;

  match mid with
  | Some ml
    => me <- entity_from_mastodon_id ml                              ;

       match me with
       | Some e
         => tok <- gen_token                                         ;
            assign_token tok (email (val e))                        ;;
            pure (Some tok)
       | None
         => pure None
       end
  | None
    => pure None
  end.