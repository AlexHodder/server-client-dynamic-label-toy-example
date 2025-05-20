module SDL.Protocol.Stateful.Proof

open Comparse
open DY.Core
open DY.Lib

open SDL.Protocol.Total
open SDL.Protocol.Total.Proof

open SDL.Protocol.Stateful

#set-options "--fuel 0 --ifuel 1 --z3rlimit 25  --z3cliopt 'smt.qi.eager_threshold=100'"

/// This module proves invariant preservation
/// for all the functions in SDL.Protocol.Stateful.

(*** Trace invariants ***)

/// The (local) state predicate.

let state_predicate_sdl : local_state_predicate sdl_session = {
  pred = (fun tr prin sess_id st ->
    match st with
    | ServerGenerateNonce server nonce i -> (
      prin == server /\
      is_knowable_by (principal_label server) tr nonce /\
      // ensure that the nonce was constructed by Rand constructor.
      Rand? nonce /\
      Rand?.time nonce == i /\
      event_triggered tr server (Generate server nonce i)
    )
    | ClientResponded server nonce -> (
      let client = prin in
      is_knowable_by (principal_label server `join` principal_label client) tr nonce /\
      event_triggered tr client (Respond client server nonce)
    )
  );
  pred_later = (fun tr1 tr2 prin sess_id st -> ());
  pred_knowable = (fun tr prin sess_id st -> ());
}

/// The (local) event predicate.

let event_predicate_sdl: event_predicate sdl_event =
  fun tr prin e ->
    match e with
    | Generate server nonce i -> (
      prin == server /\
      is_secret (reveal_principal_label i) tr nonce /\
      rand_generated_at tr i nonce /\
      reveal_event_triggered tr server server i
    )
    | Respond client server nonce -> (
      prin == client /\
      Rand? nonce /\
      (
        is_corrupt tr (reveal_principal_label (Rand?.time nonce)) \/
        event_triggered tr server (Generate server nonce (Rand?.time nonce))
      )
    )

let reveal_event_predicate_sdl : reveal_event_predicate =
  fun tr prin e ->
   True

/// List of all local state predicates.

let all_sessions = [
  pki_tag_and_invariant;
  private_keys_tag_and_invariant;
  (|local_state_sdl_session.tag, local_state_predicate_to_local_bytes_state_predicate state_predicate_sdl|);
]

/// List of all local event predicates.

let all_events = [
  mk_event_tag_and_pred event_predicate_sdl;
  mk_event_tag_and_pred reveal_event_predicate_sdl
]

/// Create the global trace invariants.

let trace_invariants_sdl: trace_invariants = {
  state_pred = mk_state_pred all_sessions;
  event_pred = mk_event_pred all_events;
}

instance protocol_invariants_sdl: protocol_invariants = {
  crypto_invs = crypto_invariants_sdl;
  trace_invs = trace_invariants_sdl;
}

/// Lemmas that the global state predicate contains all the local ones

let _ = do_split_boilerplate mk_state_pred_correct all_sessions
let _ = do_split_boilerplate mk_event_pred_correct all_events


(*** PROOFS ***)


val prepare_msg1_proof :
  tr:trace ->
  server:principal ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (sess_id, tr_out) = prepare_msg1 server tr in
    trace_invariant tr
  ))
let prepare_msg1_proof tr server =
  ()

val send_msg1_proof :
  tr:trace ->
  global_sess_id:sdl_global_sess_ids -> server:principal -> client:principal -> sess_id:state_id ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (opt_msg_id, tr_out) = send_msg1 global_sess_id server client sess_id tr in
    trace_invariant tr_out
  ))
let send_msg1_proof tr global_sess_id server client sess_id =
  match get_state server sess_id tr with
  | (Some (ServerGenerateNonce server' nonce i), tr') -> (

    assert(has_local_state_predicate state_predicate_sdl); // have to assert this

    match guard_tr (server = server') tr' with
    | (Some _, tr') -> (
      let ts = find_event_triggered_at_timestamp tr server (Generate server nonce i) in
      event_triggered_at_implies_pred #protocol_invariants_sdl event_predicate_sdl tr' ts server (Generate server nonce i);

      let (_, tr'') = trigger_reveal_event server client i tr' in

      trigger_reveal_event_trace_invariant reveal_event_predicate_sdl server client i tr';
      trigger_reveal_event_reveal_event_triggered server client i tr';

      match get_public_key server global_sess_id.pki (LongTermPkeKey "SDL.PublicKey") client tr'' with
      | (None, tr''') -> ()
      | (Some pk_client, tr''') -> (
        let (pk_nonce, tr4) = mk_rand PkeNonce (long_term_key_label server) 32 tr''' in

        compute_message1_proof tr4 server client pk_client nonce pk_nonce
      ))
    | _ -> ()

  )
  | _ -> ()

val prepare_msg2_proof :
  tr:trace ->
  global_sess_id:sdl_global_sess_ids -> client:principal -> msg_id:timestamp ->
  Lemma
  (requires trace_invariant tr)
  (ensures (
    let (sess_id, tr_out) = prepare_msg2 global_sess_id client msg_id tr in
    trace_invariant tr
  ))

let prepare_msg2_proof tr global_sess_id client msg_id =
  ()
