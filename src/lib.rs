use core::num;
use std::cmp::Ordering;
use std::ops::{Index, IndexMut};
use std::str::FromStr;

/// The error returned when a Fen String is not valid
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FenParseError;

pub struct GameState {
    board: BoardState,
    turn: Player,
    castle_state: CastleState,
    halfmove_clock: u8,
    fullmove_number: u16,
}

impl GameState {
    pub const INITIAL: &'static str = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1";
}

impl FromStr for GameState {
    type Err = FenParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut iter = s.split_ascii_whitespace();

        let board = match iter.next() {
            Some(board) => BoardState::from_str(board)?,
            None => return Err(FenParseError),
        };

        unimplemented!()
    }
}

/// Board layout in memory, indexed by column then row
/// ```text
///              columns
///        0  1  2  3  4  5  6  7
///    0  A8 B8 C8 D8 E8 F8 G8 H8
///    1  A7 B7 C7 D7 E7 F7 G7 H7
/// r  2  A6 B6 C6 D6 E6 F6 G6 H6
/// o  3  A5 B5 C5 D5 E5 F5 G5 H5
/// w  4  A4 B4 C4 D4 E4 F4 G4 H4
/// s  5  A3 B3 C3 D3 E3 F3 G3 H3
///    6  A2 B2 C2 D2 E2 F2 G2 H2
///    7  A1 B1 C1 D1 E1 F1 G1 H1
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoardState([[Square; 8]; 8]);

impl BoardState {
    fn empty() -> Self {
        Self([[Square::Empty; 8]; 8])
    }
}

impl FromStr for BoardState {
    type Err = FenParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if !s.is_ascii() {
            return Err(FenParseError);
        }

        let mut vec = Vec::with_capacity(s.len());
        for c in s.chars() {
            vec.push(FenToken::try_from(c)?);
        }

        // Start with an Empty board and place pieces as we get them
        let mut board = Self::empty();

        let mut index = SquareIndex::BEGIN;
        for token in vec {
            match token {
                FenToken::NextRank => index.next_rank()?,
                FenToken::Empty(num_empty) => index.bump(num_empty)?,
                FenToken::Black(piece) => board[index] = Square::Black(piece),
                FenToken::White(piece) => board[index] = Square::Black(piece),
            }
        }

        unimplemented!()
    }
}

impl Index<SquareIndex> for BoardState {
    type Output = Square;

    fn index(&self, index: SquareIndex) -> &Self::Output {
        &self.0[index.column as usize][index.row as usize]
    }
}

impl IndexMut<SquareIndex> for BoardState {
    fn index_mut(&mut self, index: SquareIndex) -> &mut Self::Output {
        &mut self.0[index.column as usize][index.row as usize]
    }
}

pub enum FenToken {
    NextRank,
    Empty(NumEmpty),
    Black(Piece),
    White(Piece),
}

impl TryFrom<char> for FenToken {
    type Error = FenParseError;

    fn try_from(c: char) -> Result<Self, Self::Error> {
        if !c.is_ascii() {
            return Err(FenParseError);
        }

        match c {
            '/' => Ok(Self::NextRank),
            '1' => Ok(Self::Empty(NumEmpty::One)),
            '2' => Ok(Self::Empty(NumEmpty::Two)),
            '3' => Ok(Self::Empty(NumEmpty::Three)),
            '4' => Ok(Self::Empty(NumEmpty::Four)),
            '5' => Ok(Self::Empty(NumEmpty::Five)),
            '6' => Ok(Self::Empty(NumEmpty::Six)),
            '7' => Ok(Self::Empty(NumEmpty::Seven)),
            '8' => Ok(Self::Empty(NumEmpty::Eight)),
            'P' => Ok(Self::White(Piece::Pawn)),
            'N' => Ok(Self::White(Piece::Knight)),
            'B' => Ok(Self::White(Piece::Bishop)),
            'R' => Ok(Self::White(Piece::Rook)),
            'Q' => Ok(Self::White(Piece::Queen)),
            'K' => Ok(Self::White(Piece::King)),
            'p' => Ok(Self::Black(Piece::Pawn)),
            'n' => Ok(Self::Black(Piece::Knight)),
            'b' => Ok(Self::Black(Piece::Bishop)),
            'r' => Ok(Self::Black(Piece::Rook)),
            'q' => Ok(Self::Black(Piece::Queen)),
            'k' => Ok(Self::Black(Piece::King)),
            _ => Err(FenParseError),
        }
    }
}

pub enum NumEmpty {
    One,
    Two,
    Three,
    Four,
    Five,
    Six,
    Seven,
    Eight,
}

impl From<NumEmpty> for u8 {
    fn from(val: NumEmpty) -> Self {
        match val {
            NumEmpty::One => 1,
            NumEmpty::Two => 2,
            NumEmpty::Three => 3,
            NumEmpty::Four => 4,
            NumEmpty::Five => 5,
            NumEmpty::Six => 6,
            NumEmpty::Seven => 7,
            NumEmpty::Eight => 8,
        }
    }
}

impl TryFrom<u8> for NumEmpty {
    type Error = FenParseError;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            1 => Ok(NumEmpty::One),
            2 => Ok(NumEmpty::Two),
            3 => Ok(NumEmpty::Three),
            4 => Ok(NumEmpty::Four),
            5 => Ok(NumEmpty::Five),
            6 => Ok(NumEmpty::Six),
            7 => Ok(NumEmpty::Seven),
            8 => Ok(NumEmpty::Eight),
            _ => Err(FenParseError),
        }
    }
}

// TODO: See if enums are faster
// pub enum SquareIndex {
//     A8, B8, C8, D8, E8, F8, G8, H8,
//     A7, B7, C7, D7, E7, F7, G7, H7,
//     A6, B6, C6, D6, E6, F6, G6, H6,
//     A5, B5, C5, D5, E5, F5, G5, H5,
//     A4, B4, C4, D4, E4, F4, G4, H4,
//     A3, B3, C3, D3, E3, F3, G3, H3,
//     A2, B2, C2, D2, E2, F2, G2, H2,
//     A1, B1, C1, D1, E1, F1, G1, H1,
// }

#[derive(Debug, Clone, Copy)]
pub struct SquareIndex {
    column: u8,
    row: u8,
}

impl SquareIndex {
    /// Increases column by num_empty
    ///
    /// Returns error column would go out of bounds
    fn bump(&mut self, num_empty: NumEmpty) -> Result<(), FenParseError> {
        let val: u8 = num_empty.into();

        if self.column + val > 7 {
            return Err(FenParseError);
        }

        self.column += val;
        Ok(())
    }

    /// Returns error if already at last rank
    fn next_rank(&mut self) -> Result<(), FenParseError> {
        if self.row >= 7 {
            return Err(FenParseError);
        }

        self.row += 1;
        Ok(())
    }

    pub const BEGIN: Self = Self::A8;

    pub const A8: Self = SquareIndex { column: 0, row: 0 };
    pub const B8: Self = SquareIndex { column: 1, row: 0 };
    pub const C8: Self = SquareIndex { column: 2, row: 0 };
    pub const D8: Self = SquareIndex { column: 3, row: 0 };
    pub const E8: Self = SquareIndex { column: 4, row: 0 };
    pub const F8: Self = SquareIndex { column: 5, row: 0 };
    pub const G8: Self = SquareIndex { column: 6, row: 0 };
    pub const H8: Self = SquareIndex { column: 7, row: 0 };

    pub const A7: Self = SquareIndex { column: 0, row: 1 };
    pub const B7: Self = SquareIndex { column: 1, row: 1 };
    pub const C7: Self = SquareIndex { column: 2, row: 1 };
    pub const D7: Self = SquareIndex { column: 3, row: 1 };
    pub const E7: Self = SquareIndex { column: 4, row: 1 };
    pub const F7: Self = SquareIndex { column: 5, row: 1 };
    pub const G7: Self = SquareIndex { column: 6, row: 1 };
    pub const H7: Self = SquareIndex { column: 7, row: 1 };

    pub const A6: Self = SquareIndex { column: 0, row: 2 };
    pub const B6: Self = SquareIndex { column: 1, row: 2 };
    pub const C6: Self = SquareIndex { column: 2, row: 2 };
    pub const D6: Self = SquareIndex { column: 3, row: 2 };
    pub const E6: Self = SquareIndex { column: 4, row: 2 };
    pub const F6: Self = SquareIndex { column: 5, row: 2 };
    pub const G6: Self = SquareIndex { column: 6, row: 2 };
    pub const H6: Self = SquareIndex { column: 7, row: 2 };

    pub const A5: Self = SquareIndex { column: 0, row: 3 };
    pub const B5: Self = SquareIndex { column: 1, row: 3 };
    pub const C5: Self = SquareIndex { column: 2, row: 3 };
    pub const D5: Self = SquareIndex { column: 3, row: 3 };
    pub const E5: Self = SquareIndex { column: 4, row: 3 };
    pub const F5: Self = SquareIndex { column: 5, row: 3 };
    pub const G5: Self = SquareIndex { column: 6, row: 3 };
    pub const H5: Self = SquareIndex { column: 7, row: 3 };

    pub const A4: Self = SquareIndex { column: 0, row: 4 };
    pub const B4: Self = SquareIndex { column: 1, row: 4 };
    pub const C4: Self = SquareIndex { column: 2, row: 4 };
    pub const D4: Self = SquareIndex { column: 3, row: 4 };
    pub const E4: Self = SquareIndex { column: 4, row: 4 };
    pub const F4: Self = SquareIndex { column: 5, row: 4 };
    pub const G4: Self = SquareIndex { column: 6, row: 4 };
    pub const H4: Self = SquareIndex { column: 7, row: 4 };

    pub const A3: Self = SquareIndex { column: 0, row: 5 };
    pub const B3: Self = SquareIndex { column: 1, row: 5 };
    pub const C3: Self = SquareIndex { column: 2, row: 5 };
    pub const D3: Self = SquareIndex { column: 3, row: 5 };
    pub const E3: Self = SquareIndex { column: 4, row: 5 };
    pub const F3: Self = SquareIndex { column: 5, row: 5 };
    pub const G3: Self = SquareIndex { column: 6, row: 5 };
    pub const H3: Self = SquareIndex { column: 7, row: 5 };

    pub const A2: Self = SquareIndex { column: 0, row: 6 };
    pub const B2: Self = SquareIndex { column: 1, row: 6 };
    pub const C2: Self = SquareIndex { column: 2, row: 6 };
    pub const D2: Self = SquareIndex { column: 3, row: 6 };
    pub const E2: Self = SquareIndex { column: 4, row: 6 };
    pub const F2: Self = SquareIndex { column: 5, row: 6 };
    pub const G2: Self = SquareIndex { column: 6, row: 6 };
    pub const H2: Self = SquareIndex { column: 7, row: 6 };

    pub const A1: Self = SquareIndex { column: 0, row: 7 };
    pub const B1: Self = SquareIndex { column: 1, row: 7 };
    pub const C1: Self = SquareIndex { column: 2, row: 7 };
    pub const D1: Self = SquareIndex { column: 3, row: 7 };
    pub const E1: Self = SquareIndex { column: 4, row: 7 };
    pub const F1: Self = SquareIndex { column: 5, row: 7 };
    pub const G1: Self = SquareIndex { column: 6, row: 7 };
    pub const H1: Self = SquareIndex { column: 7, row: 7 };
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Square {
    Empty,
    Black(Piece),
    White(Piece),
}

impl Square {
    pub fn value(&self) -> u8 {
        match self {
            Square::Empty => 0,
            Square::Black(p) => p.value(),
            Square::White(p) => p.value(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Piece {
    Pawn,
    Knight,
    Bishop,
    Rook,
    Queen,
    King,
}

impl Piece {
    /// From <https://www.chess.com/terms/chess-piece-value#whatareCPV>
    pub fn value(&self) -> u8 {
        match self {
            Self::Pawn => 1,
            Self::Knight => 3,
            Self::Bishop => 3,
            Self::Rook => 5,
            Self::Queen => 9,
            Self::King => 0,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Player {
    White,
    Black,
}

impl FromStr for Player {
    type Err = FenParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match &s.to_lowercase()[..] {
            "w" => Ok(Player::White),
            "b" => Ok(Player::Black),
            _ => Err(FenParseError),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct CastleState(u8);

impl CastleState {
    pub fn get_white_king_castle(&self) -> bool {
        self.get_bit(Self::WHITE_KING_SIDE_BIT)
    }

    pub fn get_white_queen_castle(&self) -> bool {
        self.get_bit(Self::WHITE_QUEEN_SIDE_BIT)
    }

    pub fn get_black_king_castle(&self) -> bool {
        self.get_bit(Self::BLACK_KING_SIDE_BIT)
    }

    pub fn get_black_queen_castle(&self) -> bool {
        self.get_bit(Self::BLACK_QUEEN_SIDE_BIT)
    }

    pub fn set_white_king_castle(&mut self, value: bool) {
        self.set_bit(Self::WHITE_KING_SIDE_BIT, value)
    }

    pub fn set_white_queen_castle(&mut self, value: bool) {
        self.set_bit(Self::WHITE_QUEEN_SIDE_BIT, value)
    }

    pub fn set_black_king_castle(&mut self, value: bool) {
        self.set_bit(Self::BLACK_KING_SIDE_BIT, value)
    }

    pub fn set_black_queen_castle(&mut self, value: bool) {
        self.set_bit(Self::BLACK_QUEEN_SIDE_BIT, value)
    }

    const WHITE_KING_SIDE_BIT: u8 = 3;
    const WHITE_QUEEN_SIDE_BIT: u8 = 2;
    const BLACK_KING_SIDE_BIT: u8 = 1;
    const BLACK_QUEEN_SIDE_BIT: u8 = 0;

    fn get_bit(&self, bit_significance: u8) -> bool {
        self.0 & (1u8 << bit_significance) != 0
    }

    fn set_bit(&mut self, bit_significance: u8, value: bool) {
        if value {
            self.0 |= 1u8 << bit_significance;
        } else {
            self.0 &= !(1u8 << bit_significance);
        }
    }
}

impl FromStr for CastleState {
    type Err = FenParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut new_ = Self(0);
        for c in s.chars() {
            match c {
                'K' => new_.set_white_king_castle(true),
                'Q' => new_.set_white_queen_castle(true),
                'k' => new_.set_black_king_castle(true),
                'q' => new_.set_black_queen_castle(true),
                _ => return Err(FenParseError),
            }
        }
        Ok(new_)
    }
}

#[cfg(test)]
mod tests {

    mod board_state {
        use std::str::FromStr;

        use crate::{BoardState, Square, SquareIndex, Piece};

        #[test]
        fn empty() {
            assert_eq!(BoardState::from_str("///////"), Ok(BoardState::empty()));
        }

        #[test]
        fn initial() {
            let board_state =
                BoardState::from_str("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR").unwrap();

            assert_eq!(board_state[SquareIndex::A8], Square::Black(Piece::Rook));
            assert_eq!(board_state[SquareIndex::B8], Square::Black(Piece::Knight));
            assert_eq!(board_state[SquareIndex::C8], Square::Black(Piece::Bishop));
            assert_eq!(board_state[SquareIndex::D8], Square::Black(Piece::Queen));
            assert_eq!(board_state[SquareIndex::E8], Square::Black(Piece::King));
            assert_eq!(board_state[SquareIndex::F8], Square::Black(Piece::Bishop));
            assert_eq!(board_state[SquareIndex::G8], Square::Black(Piece::Knight));
            assert_eq!(board_state[SquareIndex::H8], Square::Black(Piece::Rook));

            assert_eq!(board_state[SquareIndex::A7], Square::Black(Piece::Pawn));
            assert_eq!(board_state[SquareIndex::B7], Square::Black(Piece::Pawn));
            assert_eq!(board_state[SquareIndex::C7], Square::Black(Piece::Pawn));
            assert_eq!(board_state[SquareIndex::D7], Square::Black(Piece::Pawn));
            assert_eq!(board_state[SquareIndex::E7], Square::Black(Piece::Pawn));
            assert_eq!(board_state[SquareIndex::F7], Square::Black(Piece::Pawn));
            assert_eq!(board_state[SquareIndex::G7], Square::Black(Piece::Pawn));
            assert_eq!(board_state[SquareIndex::H7], Square::Black(Piece::Pawn));

            assert_eq!(board_state[SquareIndex::A6], Square::Empty);
            assert_eq!(board_state[SquareIndex::B6], Square::Empty);
            assert_eq!(board_state[SquareIndex::C6], Square::Empty);
            assert_eq!(board_state[SquareIndex::D6], Square::Empty);
            assert_eq!(board_state[SquareIndex::E6], Square::Empty);
            assert_eq!(board_state[SquareIndex::F6], Square::Empty);
            assert_eq!(board_state[SquareIndex::G6], Square::Empty);
            assert_eq!(board_state[SquareIndex::H6], Square::Empty);

            assert_eq!(board_state[SquareIndex::A5], Square::Empty);
            assert_eq!(board_state[SquareIndex::B5], Square::Empty);
            assert_eq!(board_state[SquareIndex::C5], Square::Empty);
            assert_eq!(board_state[SquareIndex::D5], Square::Empty);
            assert_eq!(board_state[SquareIndex::E5], Square::Empty);
            assert_eq!(board_state[SquareIndex::F5], Square::Empty);
            assert_eq!(board_state[SquareIndex::G5], Square::Empty);
            assert_eq!(board_state[SquareIndex::H5], Square::Empty);

            assert_eq!(board_state[SquareIndex::A4], Square::Empty);
            assert_eq!(board_state[SquareIndex::B4], Square::Empty);
            assert_eq!(board_state[SquareIndex::C4], Square::Empty);
            assert_eq!(board_state[SquareIndex::D4], Square::Empty);
            assert_eq!(board_state[SquareIndex::E4], Square::Empty);
            assert_eq!(board_state[SquareIndex::F4], Square::Empty);
            assert_eq!(board_state[SquareIndex::G4], Square::Empty);
            assert_eq!(board_state[SquareIndex::H4], Square::Empty);

            assert_eq!(board_state[SquareIndex::A3], Square::Empty);
            assert_eq!(board_state[SquareIndex::B3], Square::Empty);
            assert_eq!(board_state[SquareIndex::C3], Square::Empty);
            assert_eq!(board_state[SquareIndex::D3], Square::Empty);
            assert_eq!(board_state[SquareIndex::E3], Square::Empty);
            assert_eq!(board_state[SquareIndex::F3], Square::Empty);
            assert_eq!(board_state[SquareIndex::G3], Square::Empty);
            assert_eq!(board_state[SquareIndex::H3], Square::Empty);

            assert_eq!(board_state[SquareIndex::A2], Square::White(Piece::Pawn));
            assert_eq!(board_state[SquareIndex::B2], Square::White(Piece::Pawn));
            assert_eq!(board_state[SquareIndex::C2], Square::White(Piece::Pawn));
            assert_eq!(board_state[SquareIndex::D2], Square::White(Piece::Pawn));
            assert_eq!(board_state[SquareIndex::E2], Square::White(Piece::Pawn));
            assert_eq!(board_state[SquareIndex::F2], Square::White(Piece::Pawn));
            assert_eq!(board_state[SquareIndex::G2], Square::White(Piece::Pawn));
            assert_eq!(board_state[SquareIndex::H2], Square::White(Piece::Pawn));

            assert_eq!(board_state[SquareIndex::A1], Square::White(Piece::Rook));
            assert_eq!(board_state[SquareIndex::B1], Square::White(Piece::Knight));
            assert_eq!(board_state[SquareIndex::C1], Square::White(Piece::Bishop));
            assert_eq!(board_state[SquareIndex::D1], Square::White(Piece::King));
            assert_eq!(board_state[SquareIndex::E1], Square::White(Piece::Queen));
            assert_eq!(board_state[SquareIndex::F1], Square::White(Piece::Bishop));
            assert_eq!(board_state[SquareIndex::G1], Square::White(Piece::Knight));
            assert_eq!(board_state[SquareIndex::H1], Square::White(Piece::Rook));
        }
    }

    mod castle_state {
        use std::str::FromStr;

        use crate::CastleState;

        #[test]
        fn all() {
            let castle_state = CastleState::from_str("KQkq").unwrap();
            assert!(castle_state.get_white_king_castle());
            assert!(castle_state.get_white_queen_castle());
            assert!(castle_state.get_black_king_castle());
            assert!(castle_state.get_black_queen_castle());
        }

        #[test]
        fn order() {
            let castle_state = CastleState::from_str("QkqK").unwrap();
            assert!(castle_state.get_white_king_castle());
            assert!(castle_state.get_white_queen_castle());
            assert!(castle_state.get_black_king_castle());
            assert!(castle_state.get_black_queen_castle());
        }

        #[test]
        fn white() {
            let castle_state = CastleState::from_str("KQ").unwrap();
            dbg!(castle_state);
            assert!(castle_state.get_white_king_castle());
            assert!(castle_state.get_white_queen_castle());
            assert!(!castle_state.get_black_king_castle());
            assert!(!castle_state.get_black_queen_castle());
        }

        #[test]
        fn black() {
            let castle_state = CastleState::from_str("kq").unwrap();
            assert!(!castle_state.get_white_king_castle());
            assert!(!castle_state.get_white_queen_castle());
            assert!(castle_state.get_black_king_castle());
            assert!(castle_state.get_black_queen_castle());
        }

        
        #[test]
        fn queens() {
            let castle_state = CastleState::from_str("qQ").unwrap();
            assert!(!castle_state.get_white_king_castle());
            assert!(castle_state.get_white_queen_castle());
            assert!(!castle_state.get_black_king_castle());
            assert!(castle_state.get_black_queen_castle());
        }

        #[test]
        fn kings() {
            let castle_state = CastleState::from_str("kK").unwrap();
            assert!(castle_state.get_white_king_castle());
            assert!(!castle_state.get_white_queen_castle());
            assert!(castle_state.get_black_king_castle());
            assert!(!castle_state.get_black_queen_castle());
        }
    }

    mod player {
        use std::str::FromStr;

        use crate::Player;

        #[test]
        fn from_str() {
            assert_eq!(Player::from_str("w"), Ok(Player::White)); 
            assert_eq!(Player::from_str("b"), Ok(Player::Black)); 
            assert_eq!(Player::from_str("W"), Ok(Player::White)); 
            assert_eq!(Player::from_str("B"), Ok(Player::Black)); 
        }

        #[test]
        fn from_str_err() {
            Player::from_str("q").unwrap_err();
        }
    }

}
