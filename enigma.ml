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

let map_l_to_r _wiring _top_letter _input_pos =
  failwith "Unimplemented"

let map_refl _wiring _input_pos =
  failwith "Unimplemented"

let map_plug _plugs _c =
  failwith "Unimplemented"

let cipher_char _config _c =
  failwith "Unimplemented"

let step _config =
  failwith "Unimplemented"

let cipher _config _s =
  failwith "Unimplemented"

let hours_worked = 0
