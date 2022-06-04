
use std::str::FromStr;


pub struct GameState {
    board: BoardState,
    turn: Player,
    castle_state: CastleState,
    halfmove_clock: u8,
    fullmove_number: u16,
}

pub struct FenParseError;

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

pub struct BoardState ([[Option<Piece>; 8]; 8]);

impl FromStr for BoardState {
    type Err = FenParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        todo!()
    }
}

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

pub struct MetaState {

}

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

pub struct CastleState {
    state: u8,
}

impl CastleState {
    
    pub fn can_white_king_castle(&self) -> bool {
        self.get_bit(Self::WHITE_KING_SIDE_BIT)
    }

    pub fn can_white_queen_castle(&self) -> bool {
        self.get_bit(Self::WHITE_QUEEN_SIDE_BIT)
    }

    pub fn can_black_king_castle(&self) -> bool {
        self.get_bit(Self::BLACK_KING_SIDE_BIT)
    }

    pub fn can_black_queen_castle(&self) -> bool {
        self.get_bit(Self::BLACK_QUEEN_SIDE_BIT)
    }

    const WHITE_KING_SIDE_BIT: u8 = 3; 
    const WHITE_QUEEN_SIDE_BIT: u8 = 2;
    const BLACK_KING_SIDE_BIT: u8 = 1;
    const BLACK_QUEEN_SIDE_BIT: u8 = 0;

    fn get_bit(&self, bit_significance: u8) -> bool {
        self.state | (1u8 << bit_significance) != 0
    }
}

impl FromStr for CastleState {
    type Err = FenParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        todo!()
    }
}

