use core::fmt;
use std::ops::{Index, IndexMut};
use std::str::FromStr;

/// The error returned when a Fen String is not valid
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FenParseError;

pub struct GameState {
    pub board: BoardState,
    pub turn: Player,
    pub castle_state: CastleState,
    pub en_passant_square: EnPassantTarget,
    pub halfmove_clock: u8,
    pub fullmove_number: u16,
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

        let turn = match iter.next() {
            Some(player) => Player::from_str(player)?,
            None => return Err(FenParseError),
        };

        let castle_state = match iter.next() {
            Some(castle_state) => CastleState::from_str(castle_state)?,
            None => return Err(FenParseError),
        };

        let en_passant_square = match iter.next() {
            Some(en_passant_target) => EnPassantTarget::from_str(en_passant_target)?,
            None => return Err(FenParseError),
        };

        let halfmove_clock = match iter.next() {
            Some(halfmove_clock) => u8::from_str(halfmove_clock).map_err(|_| FenParseError)?,
            None => return Err(FenParseError),
        };
        let fullmove_number = match iter.next() {
            Some(fullmove_number) => u16::from_str(fullmove_number).map_err(|_| FenParseError)?,
            None => return Err(FenParseError),
        };

        Ok(Self {
            board,
            turn,
            castle_state,
            en_passant_square,
            halfmove_clock,
            fullmove_number,
        })
    }
}

/// Board layout, indexed by file then rank
/// ```text
///                 file
///        A  B  C  D  E  F  G  H
///    8  A8 B8 C8 D8 E8 F8 G8 H8
///    7  A7 B7 C7 D7 E7 F7 G7 H7
/// r  6  A6 B6 C6 D6 E6 F6 G6 H6
/// a  5  A5 B5 C5 D5 E5 F5 G5 H5
/// n  4  A4 B4 C4 D4 E4 F4 G4 H4
/// k  3  A3 B3 C3 D3 E3 F3 G3 H3
///    2  A2 B2 C2 D2 E2 F2 G2 H2
///    1  A1 B1 C1 D1 E1 F1 G1 H1
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoardState([Square; 64]);

impl BoardState {
    fn empty() -> Self {
        Self([Square::Empty; 64])
    }

    fn get(&self, index: SquareIndex) -> Option<&Square> {
        self.0.get(index.0 as usize)
    }

    fn get_mut(&mut self, index: SquareIndex) -> Option<&mut Square> {
        self.0.get_mut(index.0 as usize)
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

        let mut index = SquareIndex::A8;
        let mut next_must_be_next_rank = false;
        for token in vec {
            if next_must_be_next_rank {
                if token != FenToken::NextRank {
                    return Err(FenParseError);
                } else {
                    next_must_be_next_rank = false;
                }
            }

            match token {
                FenToken::NextRank => {
                    // Update index
                    let rank = index.get_rank().0;
                    if rank > Rank::MIN {
                        index.set_file_and_rank(File::A, Rank(index.get_rank().0 - 1));
                    } else {
                        // Too many NextRank tokens
                        return Err(FenParseError);
                    }
                }
                FenToken::Empty(num_empty) => {
                    // Update index
                    let next_file = index.get_file().0 + num_empty;
                    if next_file <= File::MAX {
                        index.set_file(File(next_file));
                    } else {
                        next_must_be_next_rank = true;
                    }
                }
                FenToken::Black(piece) => {
                    // Update board
                    board[index] = Square::Black(piece);

                    // Update Index
                    let next_file = index.get_file().0 + 1;
                    if next_file <= File::MAX {
                        index.set_file(File(next_file));
                    } else {
                        next_must_be_next_rank = true;
                    }
                }
                FenToken::White(piece) => {
                    // Update board
                    board[index] = Square::White(piece);

                    // Update Index
                    let next_file = index.get_file().0 + 1;
                    if next_file <= File::MAX {
                        index.set_file(File(next_file));
                    } else {
                        next_must_be_next_rank = true;
                    }
                }
            }
        }

        Ok(board)
    }
}

impl Index<SquareIndex> for BoardState {
    type Output = Square;

    fn index(&self, index: SquareIndex) -> &Self::Output {
        self.get(index).unwrap()
    }
}

impl IndexMut<SquareIndex> for BoardState {
    fn index_mut(&mut self, index: SquareIndex) -> &mut Self::Output {
        self.get_mut(index).unwrap()
    }
}

impl Index<(File, Rank)> for BoardState {
    type Output = Square;

    fn index(&self, index: (File, Rank)) -> &Self::Output {
        self.get(index.into()).unwrap()
    }
}

impl IndexMut<(File, Rank)> for BoardState {
    fn index_mut(&mut self, index: (File, Rank)) -> &mut Self::Output {
        self.get_mut(index.into()).unwrap()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FenToken {
    NextRank,
    Empty(u8),
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
            '1'..='8' => Ok(Self::Empty(c.to_digit(10).unwrap() as u8)),
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

/// ```text
///                 File
///        A  B  C  D  E  F  G  H
///      +------------------------
///    8 | 56 57 58 59 60 61 62 63
///    7 | 48 49 50 51 52 53 54 55
/// R  6 | 40 41 42 43 44 45 46 47
/// a  5 | 32 33 34 35 36 37 38 39
/// n  4 | 24 25 26 27 28 29 30 31
/// k  3 | 16 17 18 19 20 21 22 23
///    2 | 08 09 10 11 12 13 14 15
///    1 | 00 01 02 03 04 05 06 07
/// ```
///
/// Bit representation:
///
///  7 6 5 4 3 2 1 0
/// +-+-+-+-+-+-+-+-+
/// | | | | | | | | |
/// +-+-+-+-+-+-+-+-+
/// | 0 |Rank |File |
///
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SquareIndex(u8);

impl SquareIndex {
    pub const MIN: u8 = 0;
    pub const MAX: u8 = 63;

    /// Get the rank of the square specified by this index.
    ///
    /// ```
    /// use mddd::{SquareIndex, Rank};
    ///
    /// let index = SquareIndex::B6;
    /// assert_eq!(index.get_rank(), Rank::SIX);
    /// ```
    pub fn get_rank(&self) -> Rank {
        Rank((self.0 & (0x07u8 << 3)) >> 3)
    }

    /// Get the file of the square specified by this index.
    ///
    /// ```
    /// use mddd::{SquareIndex, File};
    ///
    /// let index = SquareIndex::B6;
    /// assert_eq!(index.get_file(), File::B);
    /// ```
    pub fn get_file(&self) -> File {
        File(self.0 & 0x07u8)
    }

    /// Get the rank and file of the square specified by this index.
    ///
    /// ```
    /// use mddd::{SquareIndex, File, Rank};
    ///
    /// let index = SquareIndex::B6;
    /// assert_eq!(index.get_file_and_rank(), (File::B, Rank::SIX));
    /// ```
    pub fn get_file_and_rank(&self) -> (File, Rank) {
        (self.get_file(), self.get_rank())
    }

    /// Set the rank of the square specified by this index.
    ///
    /// ```
    /// use mddd::{SquareIndex, Rank};
    ///
    /// let mut index = SquareIndex::B6;
    /// index.set_rank(Rank::THREE);
    /// assert_eq!(index, SquareIndex::B3);
    /// ```
    pub fn set_rank(&mut self, rank: Rank) {
        assert!(rank.is_valid());
        let temp = (rank.0 & 0x07) << 3;
        self.0 |= temp;
        self.0 &= temp | !(0x07 << 3);
    }

    /// Set the file of the square specified by this index.
    ///
    /// ```
    /// use mddd::{SquareIndex, File};
    ///
    /// let mut index = SquareIndex::B6;
    /// index.set_file(File::E);
    /// assert_eq!(index, SquareIndex::E6);
    /// ```
    pub fn set_file(&mut self, file: File) {
        assert!(file.is_valid());
        let temp = file.0 & 0x07;
        self.0 |= temp;
        self.0 &= temp | !0x07;
    }

    /// Set the rank and file of the square specified by this index.
    ///
    /// ```
    /// use mddd::{SquareIndex, File, Rank};
    ///
    /// let mut index = SquareIndex::B6;
    /// index.set_file_and_rank(File::E, Rank::THREE);
    /// assert_eq!(index, SquareIndex::E3);
    /// ```
    pub fn set_file_and_rank(&mut self, file: File, rank: Rank) {
        assert!(file.is_valid() && rank.is_valid());
        let temp1 = (rank.0 & 0x07) << 3;
        let temp2 = file.0 & 0x07;
        self.0 = temp1 | temp2;
    }

    pub const A1: Self = SquareIndex(00u8);
    pub const B1: Self = SquareIndex(01u8);
    pub const C1: Self = SquareIndex(02u8);
    pub const D1: Self = SquareIndex(03u8);
    pub const E1: Self = SquareIndex(04u8);
    pub const F1: Self = SquareIndex(05u8);
    pub const G1: Self = SquareIndex(06u8);
    pub const H1: Self = SquareIndex(07u8);

    pub const A2: Self = SquareIndex(08u8);
    pub const B2: Self = SquareIndex(09u8);
    pub const C2: Self = SquareIndex(10u8);
    pub const D2: Self = SquareIndex(11u8);
    pub const E2: Self = SquareIndex(12u8);
    pub const F2: Self = SquareIndex(13u8);
    pub const G2: Self = SquareIndex(14u8);
    pub const H2: Self = SquareIndex(15u8);

    pub const A3: Self = SquareIndex(16u8);
    pub const B3: Self = SquareIndex(17u8);
    pub const C3: Self = SquareIndex(18u8);
    pub const D3: Self = SquareIndex(19u8);
    pub const E3: Self = SquareIndex(20u8);
    pub const F3: Self = SquareIndex(21u8);
    pub const G3: Self = SquareIndex(22u8);
    pub const H3: Self = SquareIndex(23u8);

    pub const A4: Self = SquareIndex(24u8);
    pub const B4: Self = SquareIndex(25u8);
    pub const C4: Self = SquareIndex(26u8);
    pub const D4: Self = SquareIndex(27u8);
    pub const E4: Self = SquareIndex(28u8);
    pub const F4: Self = SquareIndex(29u8);
    pub const G4: Self = SquareIndex(30u8);
    pub const H4: Self = SquareIndex(31u8);

    pub const A5: Self = SquareIndex(32u8);
    pub const B5: Self = SquareIndex(33u8);
    pub const C5: Self = SquareIndex(34u8);
    pub const D5: Self = SquareIndex(35u8);
    pub const E5: Self = SquareIndex(36u8);
    pub const F5: Self = SquareIndex(37u8);
    pub const G5: Self = SquareIndex(38u8);
    pub const H5: Self = SquareIndex(39u8);

    pub const A6: Self = SquareIndex(40u8);
    pub const B6: Self = SquareIndex(41u8);
    pub const C6: Self = SquareIndex(42u8);
    pub const D6: Self = SquareIndex(43u8);
    pub const E6: Self = SquareIndex(44u8);
    pub const F6: Self = SquareIndex(45u8);
    pub const G6: Self = SquareIndex(46u8);
    pub const H6: Self = SquareIndex(47u8);

    pub const A7: Self = SquareIndex(48u8);
    pub const B7: Self = SquareIndex(49u8);
    pub const C7: Self = SquareIndex(50u8);
    pub const D7: Self = SquareIndex(51u8);
    pub const E7: Self = SquareIndex(52u8);
    pub const F7: Self = SquareIndex(53u8);
    pub const G7: Self = SquareIndex(54u8);
    pub const H7: Self = SquareIndex(55u8);

    pub const A8: Self = SquareIndex(56u8);
    pub const B8: Self = SquareIndex(57u8);
    pub const C8: Self = SquareIndex(58u8);
    pub const D8: Self = SquareIndex(59u8);
    pub const E8: Self = SquareIndex(60u8);
    pub const F8: Self = SquareIndex(61u8);
    pub const G8: Self = SquareIndex(62u8);
    pub const H8: Self = SquareIndex(63u8);
}

impl From<(File, Rank)> for SquareIndex {
    fn from(values: (File, Rank)) -> Self {
        let file = values.0;
        let rank = values.1;
        assert!(file.is_valid() && rank.is_valid());
        let temp1 = (rank.0 & 0x07) << 3;
        let temp2 = file.0 & 0x07;
        Self(temp1 | temp2)
    }
}

impl From<SquareIndex> for (File, Rank) {
    fn from(values: SquareIndex) -> Self {
        values.get_file_and_rank()
    }
}

impl FromStr for SquareIndex {
    type Err = FenParseError;

    /// ```
    /// use std::str::FromStr;
    /// use mddd::{SquareIndex, FenParseError};
    ///
    /// assert_eq!(SquareIndex::from_str("c1"), Ok(SquareIndex::C1));
    /// assert_eq!(SquareIndex::from_str("g2"), Ok(SquareIndex::G2));
    /// assert_eq!(SquareIndex::from_str("b4"), Ok(SquareIndex::B4));
    /// assert_eq!(SquareIndex::from_str("f7"), Ok(SquareIndex::F7));
    /// assert_eq!(SquareIndex::from_str("x9"), Err(FenParseError));
    /// ```
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if !s.is_ascii() || s.len() != 2 {
            return Err(FenParseError);
        }

        let mut iter = s.chars();

        let file = File::try_from(iter.next().unwrap())?;
        let rank = Rank::try_from(iter.next().unwrap())?;

        Ok(Self::from((file, rank)))
    }
}

impl fmt::Display for SquareIndex {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (file, rank) = self.get_file_and_rank();
        write!(f, "{}{}", file, rank)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct File(u8);

impl File {
    const MIN: u8 = 0;
    const MAX: u8 = 7;

    fn is_valid(&self) -> bool {
        File::MIN <= self.0 && self.0 <= File::MAX
    }

    pub const A: Self = File(0);
    pub const B: Self = File(1);
    pub const C: Self = File(2);
    pub const D: Self = File(3);
    pub const E: Self = File(4);
    pub const F: Self = File(5);
    pub const G: Self = File(6);
    pub const H: Self = File(7);
}

impl TryFrom<char> for File {
    type Error = FenParseError;

    fn try_from(value: char) -> Result<Self, Self::Error> {
        match value.to_ascii_lowercase() {
            'a' => Ok(Self(0)),
            'b' => Ok(Self(1)),
            'c' => Ok(Self(2)),
            'd' => Ok(Self(3)),
            'e' => Ok(Self(4)),
            'f' => Ok(Self(5)),
            'g' => Ok(Self(6)),
            'h' => Ok(Self(7)),
            _ => Err(FenParseError),
        }
    }
}

impl From<File> for char {
    fn from(value: File) -> Self {
        assert!(value.is_valid());
        match value.0 {
            0 => 'a',
            1 => 'b',
            2 => 'c',
            3 => 'd',
            4 => 'e',
            5 => 'f',
            6 => 'g',
            7 => 'h',
            _ => panic!("unhandled case"),
        }
    }
}

impl fmt::Display for File {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        char::from(*self).fmt(f)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Rank(u8);

impl Rank {
    const MIN: u8 = 0;
    const MAX: u8 = 7;

    fn is_valid(&self) -> bool {
        Rank::MIN <= self.0 && self.0 <= Rank::MAX
    }

    pub const ONE: Self = Rank(0);
    pub const TWO: Self = Rank(1);
    pub const THREE: Self = Rank(2);
    pub const FOUR: Self = Rank(3);
    pub const FIVE: Self = Rank(4);
    pub const SIX: Self = Rank(5);
    pub const SEVEN: Self = Rank(6);
    pub const EIGHT: Self = Rank(7);
}

impl TryFrom<char> for Rank {
    type Error = FenParseError;

    fn try_from(value: char) -> Result<Self, Self::Error> {
        value
            .to_digit(10)
            .map(|rank| match rank {
                1..=8 => Some(Self(rank as u8 - 1)),
                _ => None,
            })
            .flatten()
            .ok_or(FenParseError)
    }
}

impl From<Rank> for char {
    fn from(value: Rank) -> Self {
        assert!(value.is_valid());
        char::from_digit(value.0 as u32, 10).unwrap()
    }
}

impl fmt::Display for Rank {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        char::from(*self).fmt(f)
    }
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EnPassantTarget(pub Option<SquareIndex>);

impl FromStr for EnPassantTarget {
    type Err = FenParseError;

    /// ```
    /// use std::str::FromStr;
    /// use mddd::{EnPassantTarget, FenParseError, SquareIndex};
    ///
    /// assert_eq!(EnPassantTarget::from_str("-"), Ok(EnPassantTarget(None)));
    /// assert_eq!(EnPassantTarget::from_str("g1"), Ok(EnPassantTarget(Some(SquareIndex::G1))));
    /// assert_eq!(EnPassantTarget::from_str("e3"), Ok(EnPassantTarget(Some(SquareIndex::E3))));
    /// assert_eq!(EnPassantTarget::from_str("a5"), Ok(EnPassantTarget(Some(SquareIndex::A5))));
    /// assert_eq!(EnPassantTarget::from_str("b6"), Ok(EnPassantTarget(Some(SquareIndex::B6))));
    /// assert_eq!(EnPassantTarget::from_str("a8"), Ok(EnPassantTarget(Some(SquareIndex::A8))));
    /// assert_eq!(EnPassantTarget::from_str("g"), Err(FenParseError));
    /// ```
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if !s.is_ascii() {
            return Err(FenParseError);
        }

        match s.len() {
            1 => {
                if s.chars().next().unwrap() == '-' {
                    Ok(Self(None))
                } else {
                    Err(FenParseError)
                }
            }
            2 => SquareIndex::from_str(s).map(|index| Self(Some(index))),
            _ => Err(FenParseError),
        }
    }
}

#[cfg(test)]
mod tests {

    mod game_state {
        use std::str::FromStr;

        use crate::GameState;

        #[test]
        fn initial() {
            GameState::from_str(GameState::INITIAL).unwrap();
        }
    }

    mod board_state {
        use std::str::FromStr;

        use crate::{BoardState, Piece, Square, SquareIndex};

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
            assert_eq!(board_state[SquareIndex::D1], Square::White(Piece::Queen));
            assert_eq!(board_state[SquareIndex::E1], Square::White(Piece::King));
            assert_eq!(board_state[SquareIndex::F1], Square::White(Piece::Bishop));
            assert_eq!(board_state[SquareIndex::G1], Square::White(Piece::Knight));
            assert_eq!(board_state[SquareIndex::H1], Square::White(Piece::Rook));
        }

        #[test]
        fn mid_game() {
            let board_state =
                BoardState::from_str("r1b1k1nr/p2p1pNp/n2B4/1p1NP2P/6P1/3P1Q2/P1P1K3/q5b1")
                    .unwrap();

            assert_eq!(board_state[SquareIndex::A8], Square::Black(Piece::Rook));
            assert_eq!(board_state[SquareIndex::B8], Square::Empty);
            assert_eq!(board_state[SquareIndex::C8], Square::Black(Piece::Bishop));
            assert_eq!(board_state[SquareIndex::D8], Square::Empty);
            assert_eq!(board_state[SquareIndex::E8], Square::Black(Piece::King));
            assert_eq!(board_state[SquareIndex::F8], Square::Empty);
            assert_eq!(board_state[SquareIndex::G8], Square::Black(Piece::Knight));
            assert_eq!(board_state[SquareIndex::H8], Square::Black(Piece::Rook));

            assert_eq!(board_state[SquareIndex::A7], Square::Black(Piece::Pawn));
            assert_eq!(board_state[SquareIndex::B7], Square::Empty);
            assert_eq!(board_state[SquareIndex::C7], Square::Empty);
            assert_eq!(board_state[SquareIndex::D7], Square::Black(Piece::Pawn));
            assert_eq!(board_state[SquareIndex::E7], Square::Empty);
            assert_eq!(board_state[SquareIndex::F7], Square::Black(Piece::Pawn));
            assert_eq!(board_state[SquareIndex::G7], Square::White(Piece::Knight));
            assert_eq!(board_state[SquareIndex::H7], Square::Black(Piece::Pawn));

            assert_eq!(board_state[SquareIndex::A6], Square::Black(Piece::Knight));
            assert_eq!(board_state[SquareIndex::B6], Square::Empty);
            assert_eq!(board_state[SquareIndex::C6], Square::Empty);
            assert_eq!(board_state[SquareIndex::D6], Square::White(Piece::Bishop));
            assert_eq!(board_state[SquareIndex::E6], Square::Empty);
            assert_eq!(board_state[SquareIndex::F6], Square::Empty);
            assert_eq!(board_state[SquareIndex::G6], Square::Empty);
            assert_eq!(board_state[SquareIndex::H6], Square::Empty);

            assert_eq!(board_state[SquareIndex::A5], Square::Empty);
            assert_eq!(board_state[SquareIndex::B5], Square::Black(Piece::Pawn));
            assert_eq!(board_state[SquareIndex::C5], Square::Empty);
            assert_eq!(board_state[SquareIndex::D5], Square::White(Piece::Knight));
            assert_eq!(board_state[SquareIndex::E5], Square::White(Piece::Pawn));
            assert_eq!(board_state[SquareIndex::F5], Square::Empty);
            assert_eq!(board_state[SquareIndex::G5], Square::Empty);
            assert_eq!(board_state[SquareIndex::H5], Square::White(Piece::Pawn));

            assert_eq!(board_state[SquareIndex::A4], Square::Empty);
            assert_eq!(board_state[SquareIndex::B4], Square::Empty);
            assert_eq!(board_state[SquareIndex::C4], Square::Empty);
            assert_eq!(board_state[SquareIndex::D4], Square::Empty);
            assert_eq!(board_state[SquareIndex::E4], Square::Empty);
            assert_eq!(board_state[SquareIndex::F4], Square::Empty);
            assert_eq!(board_state[SquareIndex::G4], Square::White(Piece::Pawn));
            assert_eq!(board_state[SquareIndex::H4], Square::Empty);

            assert_eq!(board_state[SquareIndex::A3], Square::Empty);
            assert_eq!(board_state[SquareIndex::B3], Square::Empty);
            assert_eq!(board_state[SquareIndex::C3], Square::Empty);
            assert_eq!(board_state[SquareIndex::D3], Square::White(Piece::Pawn));
            assert_eq!(board_state[SquareIndex::E3], Square::Empty);
            assert_eq!(board_state[SquareIndex::F3], Square::White(Piece::Queen));
            assert_eq!(board_state[SquareIndex::G3], Square::Empty);
            assert_eq!(board_state[SquareIndex::H3], Square::Empty);

            assert_eq!(board_state[SquareIndex::A2], Square::White(Piece::Pawn));
            assert_eq!(board_state[SquareIndex::B2], Square::Empty);
            assert_eq!(board_state[SquareIndex::C2], Square::White(Piece::Pawn));
            assert_eq!(board_state[SquareIndex::D2], Square::Empty);
            assert_eq!(board_state[SquareIndex::E2], Square::White(Piece::King));
            assert_eq!(board_state[SquareIndex::F2], Square::Empty);
            assert_eq!(board_state[SquareIndex::G2], Square::Empty);
            assert_eq!(board_state[SquareIndex::H2], Square::Empty);

            assert_eq!(board_state[SquareIndex::A1], Square::Black(Piece::Queen));
            assert_eq!(board_state[SquareIndex::B1], Square::Empty);
            assert_eq!(board_state[SquareIndex::C1], Square::Empty);
            assert_eq!(board_state[SquareIndex::D1], Square::Empty);
            assert_eq!(board_state[SquareIndex::E1], Square::Empty);
            assert_eq!(board_state[SquareIndex::F1], Square::Empty);
            assert_eq!(board_state[SquareIndex::G1], Square::Black(Piece::Bishop));
            assert_eq!(board_state[SquareIndex::H1], Square::Empty);
        }
    }

    mod square_index {
        use crate::{File, Rank, SquareIndex};

        #[test]
        fn set_rank() {
            let mut index = SquareIndex::A1;
            index.set_rank(Rank::FIVE);
            assert_eq!(index, SquareIndex::A5);
        }

        #[test]
        fn set_file() {
            let mut index = SquareIndex::A1;
            index.set_file(File::E);
            assert_eq!(index, SquareIndex::E1);
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
