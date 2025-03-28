module SDL.Protocol.SecurityProperties

open Comparse
open DY.Core
open DY.Lib

open SDL.Protocol.Total
open SDL.Protocol.Stateful
open SDL.Protocol.Total.Proof
open SDL.Protocol.Stateful.Proof
open LabelExtension

val nonce_secrecy :
  tr:trace -> server:principal -> nonce:bytes{Rand? nonce} -> i:timestamp{i == Rand?.time nonce} ->
  Lemma
  (requires
    attacker_knows tr nonce /\
    trace_invariant tr /\ (
      (exists sess_id. state_was_set tr server sess_id (ServerGenerateNonce server nonce i)) \/
      (exists sess_id. state_was_set tr server sess_id (ClientResponded server nonce))
    )
  )
  (ensures exists client tr'.
    tr <$ tr' /\ reveal_event_triggered tr client i /\ is_corrupt tr' (principal_label client)
  )
let nonce_secrecy tr server nonce i =
  attacker_only_knows_publishable_values tr nonce;
  is_corrupt_ordered_ex_guard tr (reveal_event_triggered_label i) principal_label
