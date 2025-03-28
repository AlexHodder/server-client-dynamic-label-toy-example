module SDL.Protocol.Stateful

open Comparse
open DY.Core
open DY.Lib
open SDL.Protocol.Total

open LabelExtension

(*** State Type ***)

[@@ with_bytes bytes]
type sdl_session =
  | ServerGenerateNonce : server:principal -> nonce:bytes -> i:nat -> sdl_session
  | ClientResponded : server:principal -> nonce:bytes -> sdl_session

%splice [ps_sdl_session] (gen_parser (`sdl_session))
%splice [ps_sdl_session_is_well_formed] (gen_is_well_formed_lemma (`sdl_session))

instance parseable_serializeable_bytes_sdl_session : parseable_serializeable bytes sdl_session = mk_parseable_serializeable ps_sdl_session

instance local_state_sdl_session : local_state sdl_session = {
  tag = "SDL.Session";
  format = parseable_serializeable_bytes_sdl_session;
}

(*** Event type ***)

[@@ with_bytes bytes]
type sdl_event =
  | Generate : server:principal -> nonce:bytes -> i:nat -> sdl_event
  | Respond : client:principal -> server:principal -> nonce:bytes -> sdl_event

%splice [ps_sdl_event] (gen_parser (`sdl_event))
%splice [ps_sdl_event_is_well_formed] (gen_is_well_formed_lemma (`sdl_event))

instance event_sdl_event : event sdl_event = {
  tag = "SDL.Event";
  format = mk_parseable_serializeable ps_sdl_event;
}

(*** Stateful Code ***)

type sdl_global_sess_ids = {
  pki : state_id;
  private_keys : state_id;
}

val prepare_msg1 : principal -> traceful state_id
let prepare_msg1 server =
  let* i = get_time in
  let* nonce = mk_rand NoUsage (reveal_principal_label i) 32 in

  // reveal nonce to the server
  reveal_event server i;*

  trigger_event server (Generate server nonce i);*
  let* sess_id = new_session_id server in
  set_state server sess_id (ServerGenerateNonce server nonce i);*

  return sess_id

val send_msg1 : sdl_global_sess_ids -> principal -> principal -> state_id -> traceful (option timestamp)
let send_msg1 global_sess_id server client sess_id =
  let*? st = get_state server sess_id in
  guard_tr (ServerGenerateNonce? st);*?

  let ServerGenerateNonce server' nonce i = st in

  guard_tr(server = server');*?

  reveal_event client i;* // generate a reveal

  let*? pk_client = get_public_key server global_sess_id.pki (LongTermPkeKey "SDL.PublicKey") client in
  let* pk_nonce = mk_rand PkeNonce (long_term_key_label server) 32 in
  let msg = compute_message1 server client pk_client nonce pk_nonce in
  let* msg_id = send_msg msg in
  return (Some msg_id)

val prepare_msg2 : sdl_global_sess_ids -> principal -> timestamp -> traceful (option unit)
let prepare_msg2 global_sess_id client msg_id =
  let*? msg = recv_msg msg_id in
  let*? sk_b = get_private_key client global_sess_id.private_keys (LongTermPkeKey "SDL.PublicKey") in
  let*? msg1 : message1 = return (decode_message1 client msg sk_b) in
  trigger_event client (Respond client msg1.server msg1.nonce);*
  let* sess_id = new_session_id client in
  set_state client sess_id (ClientResponded msg1.server msg1.nonce);*
  return (Some ())
