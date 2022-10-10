use std::fs::OpenOptions;
use std::io::Write;
use std::{
    collections::{HashMap, HashSet},
    fmt::{Display, Formatter},
    fs::File,
    hash::Hash,
    io::{self, BufRead, BufReader},
};

use rand::{seq::IteratorRandom, Rng};

#[derive(Clone)]
struct TuringMachine {
    states: HashSet<State>,                                            // Q
    alphabet: HashSet<Symbol>,                                         // Σ
    tape_alphabet: HashSet<Symbol>,                                    // Γ
    transitions: HashMap<(State, Symbol), (State, Symbol, Direction)>, // δ : (Q x Γ) -> (Q x (Γ \ {Start}) x {L, R})
    other: TuringMachineOther, // s = q_0 = start_state, q_accept, q_reject
}

const START_SYMBOL_NAME: &str = "▷";
const BLANK_SYMBOL_NAME: &str = "⊔";

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
struct State(String);
#[derive(PartialEq, Eq, Hash, Clone, Debug)]
struct Symbol(String);
#[derive(PartialEq, Eq, Clone, Debug)]
enum Direction {
    Left,
    Right,
}
#[derive(Clone)]
struct TuringMachineOther {
    start_state: State,
    accept_state: State,
    reject_state: State,
}

struct TuringMachineConfiguration {
    state: State,
    tape: Vec<Symbol>,
    head: usize,
}

impl TuringMachine {
    fn new(
        states: HashSet<State>,
        alphabet: HashSet<Symbol>,
        tape_alphabet: HashSet<Symbol>,
        transitions: HashMap<(State, Symbol), (State, Symbol, Direction)>,
        other: TuringMachineOther,
    ) -> Result<Self, String> {
        // strict subset
        // Σ ⊂ Γ
        if !alphabet.is_subset(&tape_alphabet) {
            return Err("alphabet is not a subset of tape_alphabet".to_string());
        }
        // q_0 ∈ Q
        if !states.contains(&other.start_state) {
            return Err("start_state is not in states".to_string());
        }
        // q_accept ∈ Q
        if !states.contains(&other.accept_state) {
            return Err("accept_state is not in states".to_string());
        }
        // q_reject ∈ Q
        if !states.contains(&other.reject_state) {
            return Err("reject_state is not in states".to_string());
        }
        // all state, symbol pairs are in δ and the resulting state, symbol pair is in  Q x (Γ \ {Start})
        for state in states.iter() {
            for symbol in tape_alphabet.iter() {
                // we skip the accept and reject states
                if state == &other.accept_state || state == &other.reject_state {
                    continue;
                }
                let transition =
                    transitions
                        .get(&(state.clone(), symbol.clone()))
                        .ok_or(format!(
                            "transition for state {:?} and symbol {:?} is not defined",
                            state, symbol
                        ))?;
                if !states.contains(&transition.0) {
                    return Err(format!(
                        "transition for state {:?} and symbol {:?} is not in states",
                        state, symbol
                    ));
                }
                if !tape_alphabet.contains(&transition.1) {
                    // ∈ Γ
                    // start symbol is allowed to write start symbol
                    return Err(format!(
                        "transition for state {:?} and symbol {:?} is not in tape_alphabet",
                        state, symbol
                    ));
                }
                // Γ \ {Start}
                if transition.1 == Symbol(START_SYMBOL_NAME.to_string())
                    && symbol != &Symbol(START_SYMBOL_NAME.to_string())
                {
                    return Err(format!(
                        "transition for state {:?} and symbol {:?} has an invalid symbol {:?}",
                        state, symbol, transition.1
                    ));
                }
                // if it's on the start symbol, it can only go right
                if symbol == &Symbol(START_SYMBOL_NAME.to_string())
                    && transition.2 != Direction::Right
                {
                    return Err(format!(
                        "transition for state {:?} and symbol {:?} has an invalid direction {:?}",
                        state, symbol, transition.2
                    ));
                }
            }
        }
        Ok(Self {
            states,
            alphabet,
            tape_alphabet,
            transitions,
            other,
        })
    }

    fn is_valid_configuration(
        &self,
        configuration: &TuringMachineConfiguration,
    ) -> Result<(), String> {
        // q ∈ Q
        if !self.states.contains(&configuration.state) {
            return Err(format!(
                "configuration state {:?} is not in states",
                configuration.state
            ));
        }
        // ∀ i ∈ [0, |tape|), tape[i] ∈ Γ
        for symbol in configuration.tape.iter() {
            if !self.tape_alphabet.contains(symbol) {
                return Err(format!(
                    "configuration tape symbol {:?} is not in tape_alphabet",
                    symbol
                ));
            }
        }
        // 0 ≤ head < |tape|
        // if configuration.head >= configuration.tape.len() {
        //     return Err(format!(
        //         "configuration head {} is out of bounds",
        //         configuration.head
        //     ));
        // }
        Ok(())
    }
}

enum TuringMachineResult {
    Accept,
    Reject,
    Step(TuringMachineConfiguration),
}

impl TuringMachine {
    fn step(
        &self,
        mut configuration: TuringMachineConfiguration,
    ) -> Result<TuringMachineResult, String> {
        #[cfg(debug_assertions)]
        self.is_valid_configuration(&configuration)?;
        let symbol_at_head = {
            // if the head is at the end of the tape, add a blank symbol
            if configuration.head == configuration.tape.len() {
                configuration
                    .tape
                    .push(Symbol(BLANK_SYMBOL_NAME.to_string()));
            }
            configuration.tape[configuration.head].clone()
        };
        let transition = self
            .transitions
            .get(&(configuration.state.clone(), symbol_at_head.clone()))
            .ok_or(format!(
                "transition for state {:?} and symbol {:?} is not defined",
                configuration.state, symbol_at_head
            ))?;
        // update the state
        configuration.state = transition.0.clone();
        // update the symbol at the head
        configuration.tape[configuration.head] = transition.1.clone();
        configuration.head = match transition.2 {
            Direction::Left => configuration.head - 1,
            Direction::Right => configuration.head + 1,
        };
        // if the head is at the end of the tape, add a blank symbol
        if configuration.head == configuration.tape.len() {
            configuration
                .tape
                .push(Symbol(BLANK_SYMBOL_NAME.to_string()));
        }

        if configuration.state == self.other.accept_state {
            Ok(TuringMachineResult::Accept)
        } else if configuration.state == self.other.reject_state {
            Ok(TuringMachineResult::Reject)
        } else {
            Ok(TuringMachineResult::Step(configuration))
        }
    }

    #[allow(dead_code)]
    fn run_until_accept_or_reject(
        &self,
        mut configuration: TuringMachineConfiguration,
    ) -> Result<TuringMachineResult, String> {
        loop {
            match self.step(configuration)? {
                TuringMachineResult::Accept => return Ok(TuringMachineResult::Accept),
                TuringMachineResult::Reject => return Ok(TuringMachineResult::Reject),
                TuringMachineResult::Step(new_configuration) => configuration = new_configuration,
            }
        }
    }

    #[allow(dead_code)]
    fn run_until_accept_or_reject_or_max_steps(
        &self,
        mut configuration: TuringMachineConfiguration,
        max_steps: usize,
    ) -> Result<TuringMachineResult, String> {
        for _ in 0..max_steps {
            match self.step(configuration)? {
                TuringMachineResult::Accept => return Ok(TuringMachineResult::Accept),
                TuringMachineResult::Reject => return Ok(TuringMachineResult::Reject),
                TuringMachineResult::Step(new_configuration) => configuration = new_configuration,
            }
        }
        Ok(TuringMachineResult::Reject)
    }

    fn run_until_accept_or_reject_or_max_steps_with_callback(
        &self,
        mut configuration: TuringMachineConfiguration,
        max_steps: usize,
        callback: &mut dyn FnMut(&TuringMachineConfiguration),
    ) -> Result<TuringMachineResult, String> {
        for _ in 0..max_steps {
            callback(&configuration);
            match self.step(configuration)? {
                TuringMachineResult::Accept => return Ok(TuringMachineResult::Accept),
                TuringMachineResult::Reject => return Ok(TuringMachineResult::Reject),
                TuringMachineResult::Step(new_configuration) => configuration = new_configuration,
            }
        }
        Ok(TuringMachineResult::Step(configuration))
    }

    fn run_until_accept_or_reject_or_max_steps_with_print(
        &self,
        configuration: TuringMachineConfiguration,
        max_steps: usize,
    ) -> Result<TuringMachineResult, String> {
        self.run_until_accept_or_reject_or_max_steps_with_callback(
            configuration,
            max_steps,
            &mut |configuration| {
                println!("{}", configuration);
            },
        )
    }
}

impl Display for TuringMachine {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "states: {:?}", self.states)?;
        writeln!(f, "alphabet: {:?}", self.alphabet)?;
        writeln!(f, "tape_alphabet: {:?}", self.tape_alphabet)?;
        writeln!(f, "transitions: {:?}", self.transitions)?;
        writeln!(f, "start_state: {:?}", self.other.start_state)?;
        writeln!(f, "accept_state: {:?}", self.other.accept_state)?;
        writeln!(f, "reject_state: {:?}", self.other.reject_state)?;
        Ok(())
    }
}

impl Display for TuringMachineConfiguration {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "state: {}; tape:", self.state.0)?;
        for (i, symbol) in self.tape.iter().enumerate() {
            if i == self.head {
                write!(f, "[{}]", symbol.0)?;
            } else {
                write!(f, " {} ", symbol.0)?;
            }
        }
        writeln!(f)?;
        for _ in 0..self.head {
            write!(f, "   ")?;
        }
        write!(f, " ^ ")?;
        Ok(())
    }
}

impl TuringMachine {
    fn new_configuration(&self, input: &str) -> Result<TuringMachineConfiguration, String> {
        let mut tape = vec![Symbol(START_SYMBOL_NAME.to_string())];
        for c in input.chars() {
            tape.push(Symbol(c.to_string()));
        }
        // check validity of input
        let configuration = TuringMachineConfiguration {
            state: self.other.start_state.clone(),
            tape,
            head: 0,
        };
        self.is_valid_configuration(&configuration)?;
        Ok(configuration)
    }
}

fn main() {
    let alphabet = ["0", "1"];
    let tape_alphabet = ["0", "1", START_SYMBOL_NAME, BLANK_SYMBOL_NAME];
    let states = ["q0", "q1", "q2", "q3", "q4", "q5", "q6", "q7"];
    let alphabet: HashSet<Symbol> =
        HashSet::from_iter(alphabet.iter().cloned().map(|s| Symbol(s.to_string())));
    let tape_alphabet: HashSet<Symbol> =
        HashSet::from_iter(tape_alphabet.iter().cloned().map(|s| Symbol(s.to_string())));
    let states: HashSet<State> =
        HashSet::from_iter(states.iter().cloned().map(|s| State(s.to_string())));
    let start_state = State("q0".to_string());
    let accept_state = State("q6".to_string());
    let reject_state = State("q7".to_string());
    let transitions = read_transition_from_file("transitions.txt", &states, &alphabet).unwrap();
    let other = TuringMachineOther {
        start_state,
        accept_state,
        reject_state,
    };
    let turing_machine =
        TuringMachine::new(states, alphabet.clone(), tape_alphabet, transitions, other).unwrap();
    // read tape(s) from stdin
    let stdin = io::stdin();
    #[allow(clippy::significant_drop_in_scrutinee)]
    for line in stdin.lock().lines() {
        let input = line.unwrap();
        let configuration = turing_machine.new_configuration(&input).unwrap();
        let result =
            turing_machine.run_until_accept_or_reject_or_max_steps_with_print(configuration, 1000);
        match result {
            Ok(TuringMachineResult::Accept) => println!("accept"),
            Ok(TuringMachineResult::Reject) => println!("reject"),
            Ok(TuringMachineResult::Step(c)) => println!("step: {}", c),
            Err(e) => println!("error: {}", e),
        }
    }
    // open out.txt and create if not exist
    // let file = OpenOptions::new()
    //     .write(true)
    //     .truncate(true)
    //     .create(true)
    //     .open("out.txt")
    //     .unwrap();
    // let run_turing_machine_for_input = |input: &str| {
    //     let configuration = turing_machine.new_configuration(input).unwrap();
    //     turing_machine.run_until_accept_or_reject_or_max_steps_with_callback(
    //         configuration,
    //         1_000_000,
    //         &mut |configuration| {
    //             // println!("{}", configuration);
    //             writeln!(&file, "{}", configuration).unwrap();
    //         },
    //     )
    // };
    // // test for random palindromes
    // let mut rng = rand::thread_rng();
    // let palindromes = (0..10)
    //     .map(|_| {
    //         let is_odd = rng.gen_bool(0.5);
    //         let length = rng.gen_range(1..=10);
    //         let mut palindrome = String::new();
    //         for _ in 0..length {
    //             // choose random symbol from alphabet
    //             let symbol = &alphabet.iter().choose(&mut rng).unwrap();
    //             palindrome.push_str(&symbol.0);
    //         }
    //         if is_odd {
    //             palindrome.push_str(&alphabet.iter().choose(&mut rng).unwrap().0);
    //         }
    //         // reverse palindrome
    //         palindrome.push_str(&palindrome.chars().rev().collect::<String>());
    //         palindrome
    //     })
    //     .collect::<Vec<_>>();
    // let non_palindromes = (0..10)
    //     .map(|_| {
    //         loop {
    //             // generate random string until not a palindrome
    //             let length = rng.gen_range(1..=10);
    //             let mut not_palindrome = String::new();
    //             for _ in 0..length {
    //                 // choose random symbol from alphabet
    //                 let symbol = &alphabet.iter().choose(&mut rng).unwrap();
    //                 not_palindrome.push_str(&symbol.0);
    //             }
    //             // check if palindrome
    //             let is_palindrome = check_palindrome(&not_palindrome);
    //             if !is_palindrome {
    //                 return not_palindrome;
    //             }
    //         }
    //     })
    //     .collect::<Vec<_>>();
    // // test for palindromes
    // for palindrome in palindromes {
    //     let result = run_turing_machine_for_input(&palindrome);
    //     match result {
    //         Ok(TuringMachineResult::Accept) => {
    //             writeln!(&file, "accept: {}", palindrome).unwrap();
    //         }
    //         Ok(TuringMachineResult::Reject) => {
    //             panic!("palindrome {} rejected", palindrome);
    //         }
    //         Ok(TuringMachineResult::Step(c)) => {
    //             panic!("palindrome {} stopped after {} steps", palindrome, c);
    //         }
    //         Err(e) => {
    //             panic!("palindrome {} error: {}", palindrome, e);
    //         }
    //     }
    // }
    // // test for non-palindromes
    // for non_palindrome in non_palindromes {
    //     let result = run_turing_machine_for_input(&non_palindrome);
    //     match result {
    //         Ok(TuringMachineResult::Accept) => {
    //             panic!("non-palindrome {} accepted", non_palindrome);
    //         }
    //         Ok(TuringMachineResult::Reject) => {
    //             writeln!(&file, "reject: {}", non_palindrome).unwrap();
    //         }
    //         Ok(TuringMachineResult::Step(c)) => {
    //             panic!(
    //                 "non-palindrome {} stopped after {} steps",
    //                 non_palindrome, c
    //             );
    //         }
    //         Err(e) => {
    //             panic!("non-palindrome {} error: {}", non_palindrome, e);
    //         }
    //     }
    // }
}

fn check_palindrome(input: &str) -> bool {
    // check if same as reversed
    let mut chars = input.chars();
    let mut chars_rev = input.chars().rev();
    loop {
        match (chars.next(), chars_rev.next()) {
            (Some(c), Some(c_rev)) => {
                if c != c_rev {
                    return false;
                }
            }
            (None, None) => return true,
            _ => return false,
        }
    }
}

type TransitionInput = (State, Symbol);
type TransitionOutput = (State, Symbol, Direction);

fn read_transition_from_file(
    file_name: &str,
    states: &HashSet<State>,
    alphabet: &HashSet<Symbol>,
) -> Result<HashMap<TransitionInput, TransitionOutput>, String> {
    let mut transitions = HashMap::new();
    let file = File::open(file_name).map_err(|e| e.to_string())?;
    let reader = BufReader::new(file);
    // read lines
    for line in reader.lines() {
        let line = line.map_err(|e| e.to_string())?;
        // if the line is blank or begins with a #, skip it
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let parts = line.split_whitespace();
        // we expect 5 parts
        let parts: Vec<&str> = parts.collect();
        if parts.len() != 5 {
            return Err(format!("invalid line: {}", line));
        }
        // if state is * then it is a wildcard
        let input_states: Vec<State> = if parts[0] == "*" {
            states.iter().cloned().collect()
        } else {
            vec![State(parts[0].to_string())]
        };
        // if symbol is * then it is a wildcard
        let input_symbols: Vec<Symbol> = if parts[1] == "*" {
            alphabet.iter().cloned().collect()
        } else {
            vec![Symbol(parts[1].to_string())]
        };
        // other parts are never wildcards
        let new_state = State(parts[2].to_string());
        let new_symbol = Symbol(parts[3].to_string());
        let direction = match parts[4] {
            "L" | "l" => Direction::Left,
            "R" | "r" => Direction::Right,
            _ => return Err(format!("invalid direction: {}", parts[4])),
        };
        // add transition(s)
        for input_state in input_states {
            for input_symbol in &input_symbols {
                transitions.insert(
                    (input_state.clone(), input_symbol.clone()),
                    (new_state.clone(), new_symbol.clone(), direction.clone()),
                );
            }
        }
    }
    Ok(transitions)
}
