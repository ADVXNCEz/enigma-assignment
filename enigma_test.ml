open OUnit2
open Enigma

let identity = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
let swap_ab = "BACDEFGHIJKLMNOPQRSTUVWXYZ"
let rotor_I = "EKMFLGDQVZNTOWYHXUSPAIBRCJ"
let rotor_III = "BDFHJLCPRTXVZNYEIWGAKMUSQO"
let refl_B = "YRUHQSLDPXNGOKMIEBFZCWVJAT"
let refl_C = "FVPJIAOYEDRZXWGCTKUQSBNMHL"

let index_test name input expected =
  name >:: fun _ ->
    assert_equal expected (index input)

let map_r_to_l_test name wiring top_letter input_pos expected =
  name >:: fun _ ->
    assert_equal expected (map_r_to_l wiring top_letter input_pos)
      ~printer:string_of_int

let map_l_to_r_test name wiring top_letter input_pos expected =
  name >:: fun _ ->
    assert_equal expected (map_l_to_r wiring top_letter input_pos)
      ~printer:string_of_int

(** [round_trip_test name wiring top_letter] checks that [map_l_to_r]
    undoes [map_r_to_l] at every position for [wiring] and [top_letter]. *)
let round_trip_test name wiring top_letter =
  name >:: fun _ ->
    List.iter
      (fun pos ->
        assert_equal pos
          (map_l_to_r wiring top_letter (map_r_to_l wiring top_letter pos))
          ~printer:string_of_int)
      (List.init 26 Fun.id)

let map_refl_test name wiring input_pos expected =
  name >:: fun _ ->
    assert_equal expected (map_refl wiring input_pos)
      ~printer:string_of_int

(** [refl_symmetry_test name wiring] checks that reflecting twice returns
    the original position, for every position. *)
let refl_symmetry_test name wiring =
  name >:: fun _ ->
    List.iter
      (fun pos ->
        assert_equal pos (map_refl wiring (map_refl wiring pos))
          ~printer:string_of_int)
      (List.init 26 Fun.id)

let map_plug_test name plugs input expected =
  name >:: fun _ ->
    assert_equal expected (map_plug plugs input)
      ~printer:(String.make 1)

let az = [('A', 'Z')]
let az_xy = [('A', 'Z'); ('X', 'Y')]
let yx_za = [('Y', 'X'); ('Z', 'A')]

let alphabet = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

(** [oriented wiring turnover top_letter] is a rotor showing [top_letter]. *)
let oriented wiring turnover top_letter =
  { rotor = { wiring; turnover }; top_letter }

(** No rotors, identity reflector, empty plugboard. *)
let bare_config = { refl = identity; rotors = []; plugboard = [] }

(** Reflector B, rotors I-II-III at AAA, empty plugboard. *)
let historical_aaa = {
  refl = refl_B;
  rotors = [
    oriented rotor_I 'Q' 'A';
    oriented "AJDKSIRUXBLHWTMCQGZNPYFVOE" 'E' 'A';
    oriented rotor_III 'V' 'A';
  ];
  plugboard = [];
}

let cipher_char_test name config input expected =
  name >:: fun _ ->
    assert_equal expected (cipher_char config input)
      ~printer:(String.make 1)

(** [cipher_alphabet_test name config expected] checks [cipher_char] on
    every letter A-Z against the matching letter of [expected]. *)
let cipher_alphabet_test name config expected =
  name >:: fun _ ->
    assert_equal expected (String.map (cipher_char config) alphabet)
      ~printer:Fun.id

let index_tests = [
  index_test "index of A is 0" 'A' 0;
  index_test "index of Z is 25" 'Z' 25;
  index_test "index of M is 12" 'M' 12;
]

let map_r_to_l_tests = [
  map_r_to_l_test "identity, top A, 0 -> 0" identity 'A' 0 0;
  map_r_to_l_test "identity, top A, 25 -> 25" identity 'A' 25 25;
  map_r_to_l_test "identity, top K, 5 -> 5" identity 'K' 5 5;
  map_r_to_l_test "swap AB, top A, 0 -> 1" swap_ab 'A' 0 1;
  map_r_to_l_test "swap AB, top A, 1 -> 0" swap_ab 'A' 1 0;
  map_r_to_l_test "swap AB, top B, 0 -> 25" swap_ab 'B' 0 25;
  map_r_to_l_test "swap AB, top B, 25 -> 0" swap_ab 'B' 25 0;
  map_r_to_l_test "swap AB, top C, 0 -> 0" swap_ab 'C' 0 0;
  map_r_to_l_test "swap AB, top C, 25 -> 24" swap_ab 'C' 25 24;
  map_r_to_l_test "rotor I, top A, 0 -> 4" rotor_I 'A' 0 4;
  map_r_to_l_test "rotor I, top B, 0 -> 9" rotor_I 'B' 0 9;
  map_r_to_l_test "rotor III, top O, 14 -> 17" rotor_III 'O' 14 17;
]

let map_l_to_r_tests = [
  map_l_to_r_test "identity, top A, 0 -> 0" identity 'A' 0 0;
  map_l_to_r_test "identity, top K, 5 -> 5" identity 'K' 5 5;
  map_l_to_r_test "swap AB, top A, 0 -> 1" swap_ab 'A' 0 1;
  map_l_to_r_test "swap AB, top A, 1 -> 0" swap_ab 'A' 1 0;
  map_l_to_r_test "swap AB, top B, 0 -> 25" swap_ab 'B' 0 25;
  map_l_to_r_test "swap AB, top B, 25 -> 0" swap_ab 'B' 25 0;
  map_l_to_r_test "rotor I, top A, 0 -> 20" rotor_I 'A' 0 20;
  map_l_to_r_test "rotor I, top A, 4 -> 0" rotor_I 'A' 4 0;
  map_l_to_r_test "rotor I, top F, 10 -> 14" rotor_I 'F' 10 14;
  map_l_to_r_test "rotor III, top O, 17 -> 14" rotor_III 'O' 17 14;
  round_trip_test "rotor I, top Q, l_to_r undoes r_to_l" rotor_I 'Q';
  round_trip_test "rotor III, top Z, l_to_r undoes r_to_l" rotor_III 'Z';
]

let map_refl_tests = [
  map_refl_test "identity reflector, 0 -> 0" identity 0 0;
  map_refl_test "identity reflector, 1 -> 1" identity 1 1;
  map_refl_test "identity reflector, 25 -> 25" identity 25 25;
  map_refl_test "reflector B, 0 -> 24" refl_B 0 24;
  map_refl_test "reflector B, 24 -> 0" refl_B 24 0;
  map_refl_test "reflector B, 5 -> 18" refl_B 5 18;
  map_refl_test "reflector C, 0 -> 5" refl_C 0 5;
  map_refl_test "reflector C, 5 -> 0" refl_C 5 0;
  refl_symmetry_test "reflector B is symmetric" refl_B;
  refl_symmetry_test "reflector C is symmetric" refl_C;
]

let map_plug_tests = [
  map_plug_test "empty plugboard, A -> A" [] 'A' 'A';
  map_plug_test "empty plugboard, Q -> Q" [] 'Q' 'Q';
  map_plug_test "A-Z, A -> Z" az 'A' 'Z';
  map_plug_test "A-Z, Z -> A" az 'Z' 'A';
  map_plug_test "A-Z, unplugged B -> B" az 'B' 'B';
  map_plug_test "A-Z X-Y, A -> Z" az_xy 'A' 'Z';
  map_plug_test "A-Z X-Y, Z -> A" az_xy 'Z' 'A';
  map_plug_test "A-Z X-Y, X -> Y" az_xy 'X' 'Y';
  map_plug_test "A-Z X-Y, Y -> X" az_xy 'Y' 'X';
  map_plug_test "A-Z X-Y, unplugged M -> M" az_xy 'M' 'M';
  map_plug_test "reordered Y-X Z-A, A -> Z" yx_za 'A' 'Z';
  map_plug_test "reordered Y-X Z-A, X -> Y" yx_za 'X' 'Y';
]

let cipher_char_tests = [
  cipher_char_test "bare machine, A -> A" bare_config 'A' 'A';
  cipher_char_test "bare machine, Z -> Z" bare_config 'Z' 'Z';
  cipher_alphabet_test "bare machine is identity" bare_config alphabet;
  cipher_char_test "historical AAA, G -> P" historical_aaa 'G' 'P';
  cipher_char_test "historical AAA, P -> G" historical_aaa 'P' 'G';
  cipher_char_test "historical AAA, A -> U" historical_aaa 'A' 'U';
  cipher_alphabet_test "historical AAA, whole alphabet" historical_aaa
    "UEJOBTPZWCNSRKDGVMLFAQIYXH";
  cipher_char_test "historical AAA + A-Z plug, A -> H"
    { historical_aaa with plugboard = az } 'A' 'H';
  cipher_char_test "historical AAA + A-Z plug, U -> Z"
    { historical_aaa with plugboard = az } 'U' 'Z';
  cipher_char_test "bare machine + A-Z plug, A -> A"
    { bare_config with plugboard = az } 'A' 'A';
]

let suite =
  "Enigma test suite" >::: List.flatten [
    index_tests;
    map_r_to_l_tests;
    map_l_to_r_tests;
    map_refl_tests;
    map_plug_tests;
    cipher_char_tests;
  ]

let () = run_test_tt_main suite
