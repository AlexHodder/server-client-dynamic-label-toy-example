module SDL.Protocol.Total.Proof

open Comparse
open DY.Core
open DY.Lib

open SDL.Protocol.Total
open SDL.Protocol.Stateful

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Cryptographic invariants ***)

instance crypto_usages_sdl : crypto_usages = default_crypto_usages

#push-options "--ifuel 2 --fuel 0"
val crypto_predicates_sdl: crypto_predicates
let crypto_predicates_sdl = {
  default_crypto_predicates with

  pke_pred = {
    pred = (fun tr sk_usage pk msg ->
      (exists prin. sk_usage == long_term_key_type_to_usage (LongTermPkeKey "SDL.PublicKey") prin /\ (
        match parse message msg with
        | Some (Msg1 msg1) -> (
          let (server, client) = (msg1.server, prin) in
          Rand? msg1.nonce /\
          (
            let i = Rand?.time msg1.nonce in
            event_triggered tr server (Generate server msg1.nonce i) /\
            get_label tr msg1.nonce == reveal_principal_label i /\
            get_label tr msg1.nonce `can_flow tr` (principal_label server `join` principal_label client) // could be derived from triggering of some reveal_event
          )

        )
        | None -> False
      ))
    );
    pred_later = (fun tr1 tr2 sk_usage pk msg ->
      parse_wf_lemma message (bytes_well_formed tr1) msg
    );
  };
}
#pop-options

instance crypto_invariants_sdl : crypto_invariants = {
  usages = crypto_usages_sdl;
  preds = crypto_predicates_sdl;
}

val compute_message1_proof :
  tr:trace ->
  server:principal -> client:principal -> pk_client:bytes -> nonce:bytes{Rand? nonce} -> pk_nonce:bytes ->
  Lemma
  (requires (
    let i = Rand?.time nonce in
    event_triggered tr server (Generate server nonce i) /\
    is_secret (reveal_principal_label i) tr nonce /\
    is_secret (long_term_key_label server) tr pk_nonce /\
    pk_nonce `has_usage tr` PkeNonce /\
    is_public_key_for tr pk_client (LongTermPkeKey "SDL.PublicKey") client /\
    reveal_event_triggered tr server server i /\
    reveal_event_triggered tr server client i
  ))
  (ensures is_publishable tr (compute_message1 server client pk_client nonce pk_nonce))
let compute_message1_proof tr server client pk_client nonce pk_nonce =
  let msg = Msg1 {server; nonce} in
  let i = Rand?.time nonce in
  reveal_principal_label_can_flow_to_principal_label tr server server i;
  reveal_principal_label_can_flow_to_principal_label tr server client i;

  serialize_wf_lemma message (is_knowable_by (long_term_key_label server) tr) msg;
  serialize_wf_lemma message (is_knowable_by (long_term_key_label client) tr) msg

val decode_message1_proof :
  tr:trace ->
  client:principal -> msg_cipher:bytes -> sk_client:bytes ->
  Lemma
  (requires
    bytes_invariant tr msg_cipher /\
    is_private_key_for tr sk_client (LongTermPkeKey "SDL.PublicKey") client
  )
  (ensures (
    match decode_message1 client msg_cipher sk_client with
    | None -> True
    | Some msg1 -> (
      is_knowable_by (principal_label msg1.server `join` principal_label client) tr msg1.nonce
    )
  ))
let decode_message1_proof tr client msg_cipher sk_client =
  match decode_message1 client msg_cipher sk_client with
  | None -> ()
  | Some msg1 -> (
    let Some msg = pke_dec sk_client msg_cipher in
    FStar.Classical.move_requires (parse_wf_lemma message (is_publishable tr)) msg;
    FStar.Classical.move_requires (parse_wf_lemma message (bytes_invariant tr)) msg
  )
