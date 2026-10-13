open OUnit2
open Enigma

let identity = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
let swap_ab = "BACDEFGHIJKLMNOPQRSTUVWXYZ"
let rotor_I = "EKMFLGDQVZNTOWYHXUSPAIBRCJ"
let rotor_III = "BDFHJLCPRTXVZNYEIWGAKMUSQO"

let index_test name input expected =
  name >:: fun _ ->
    assert_equal expected (index input)

let map_r_to_l_test name wiring top_letter input_pos expected =
  name >:: fun _ ->
    assert_equal expected (map_r_to_l wiring top_letter input_pos)
      ~printer:string_of_int

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

let suite =
  "Enigma test suite" >::: List.flatten [
    index_tests;
    map_r_to_l_tests;
  ]

let () = run_test_tt_main suite
