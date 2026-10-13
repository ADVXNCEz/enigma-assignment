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

let suite =
  "Enigma test suite" >::: List.flatten [
    index_tests;
    map_r_to_l_tests;
    map_l_to_r_tests;
  ]

let () = run_test_tt_main suite
