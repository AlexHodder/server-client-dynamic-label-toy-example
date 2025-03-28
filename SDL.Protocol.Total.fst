module SDL.Protocol.Total

open Comparse
open DY.Core
open DY.Lib

/// Protocol Outline
///
/// S -> C : {server, nonce}K_PC
/// C -> S : {confirm}K_PS

[@@ with_bytes bytes]
type message1 = {
  server: principal;
  nonce: bytes;
}

%splice [ps_message1] (gen_parser (`message1))
%splice [ps_message1_is_well_formed] (gen_is_well_formed_lemma (`message1))

[@@ with_bytes bytes]
type message2 = {
  client: principal;
}

%splice [ps_message2] (gen_parser (`message2))
%splice [ps_message2_is_well_formed] (gen_is_well_formed_lemma (`message2))

[@@ with_bytes bytes]
type message =
  | Msg1 : message1 -> message
  // | Msg2 : message2 -> message

%splice [ps_message] (gen_parser (`message))
%splice [ps_message_is_well_formed] (gen_is_well_formed_lemma (`message))

instance parseable_serializeable_bytes_message: parseable_serializeable bytes message = mk_parseable_serializeable ps_message

(*** Message 1 ***)

/// Server generates message 1

val compute_message1: principal -> principal -> bytes -> bytes -> bytes -> bytes
let compute_message1 server client pk_client nonce pk_nonce =
  let msg = Msg1 {nonce; server;} in
  pke_enc pk_client pk_nonce (serialize message msg)

/// Client process message 1

val decode_message1: principal -> bytes -> bytes -> option message1
let decode_message1 client msg1_cipher sk_client =
  let? msg1_plain = pke_dec sk_client msg1_cipher in
  let? msg1 = parse message msg1_plain in
  guard (Msg1? msg1);?
  let Msg1 message1 = msg1 in
  guard (Rand? message1.nonce);?
  Some message1

// (*** Message 2 ***)

// /// Client generates message 2

// val compute_message2: principal -> message1 -> bytes -> bytes -> bytes
// let compute_message2 client msg1 pk_server pk_nonce =
//   let msg2 = Msg2 {client;} in
//   pke_enc pk_server pk_nonce (serialize message msg2)

// /// Server process message 2

// val decode_message2: principal -> principal -> bytes -> bytes -> option (message2)
// let decode_message2 server client msg2_cipher sk_server =
//   let? msg2_plain = pke_dec sk_server msg2_cipher in
//   let? msg2 = parse _ msg2_plain in
//   guard (Msg2? msg2);?
//   let (Msg2 msg2) = msg2 in
//   guard (client = msg2.client);?
//   Some msg2
