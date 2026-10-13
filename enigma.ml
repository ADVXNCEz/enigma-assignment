type rotor = {
  wiring : string;
  turnover : char;
}

type oriented_rotor = {
  rotor : rotor;
  top_letter : char;
}

type config = {
  refl : string;
  rotors : oriented_rotor list;
  plugboard : (char * char) list;
}

let index c =
  Char.code c - Char.code 'A'

(** [wrap n] is [n] reduced into the range [0] through [25].
    Unlike [n mod 26], it is never negative. *)
let wrap n =
  ((n mod 26) + 26) mod 26

(** [to_contact top_letter pos] is the rotor contact touched by external
    position [pos] when the rotor shows [top_letter]. *)
let to_contact top_letter pos =
  wrap (pos + index top_letter)

(** [to_external top_letter contact] is the external position reached
    from rotor contact [contact] when the rotor shows [top_letter]. *)
let to_external top_letter contact =
  wrap (contact - index top_letter)

let map_r_to_l wiring top_letter input_pos =
  let contact = to_contact top_letter input_pos in
  to_external top_letter (index wiring.[contact])

(** [letter i] is the uppercase letter at alphabet index [i].
    Inverse of [index]. Requires: [i] is in [0] through [25]. *)
let letter i =
  Char.chr (i + Char.code 'A')

let map_l_to_r wiring top_letter input_pos =
  let contact = to_contact top_letter input_pos in
  to_external top_letter (String.index wiring (letter contact))

(* A reflector is a rotor that never turns, so it always shows 'A'. *)
let map_refl wiring input_pos =
  map_r_to_l wiring 'A' input_pos

let rec map_plug plugs c =
  match plugs with
  | [] -> c
  | (a, b) :: _ when a = c -> b
  | (a, b) :: _ when b = c -> a
  | _ :: rest -> map_plug rest c

(** [map_rotors_r_to_l rotors pos] passes [pos] right to left through
    [rotors], which are listed left to right. The rightmost rotor is
    applied first, so the recursive call runs before the head rotor. *)
let rec map_rotors_r_to_l rotors pos =
  match rotors with
  | [] -> pos
  | r :: rest ->
    map_r_to_l r.rotor.wiring r.top_letter (map_rotors_r_to_l rest pos)

(** [map_rotors_l_to_r rotors pos] passes [pos] left to right through
    [rotors], which are listed left to right. The leftmost rotor is
    applied first, so the head rotor runs before the recursive call. *)
let rec map_rotors_l_to_r rotors pos =
  match rotors with
  | [] -> pos
  | r :: rest ->
    map_rotors_l_to_r rest (map_l_to_r r.rotor.wiring r.top_letter pos)

let cipher_char config c =
  let pos = index (map_plug config.plugboard c) in
  let pos = map_rotors_r_to_l config.rotors pos in
  let pos = map_refl config.refl pos in
  let pos = map_rotors_l_to_r config.rotors pos in
  map_plug config.plugboard (letter pos)

let step _config =
  failwith "Unimplemented"

let cipher _config _s =
  failwith "Unimplemented"

let hours_worked = 0
