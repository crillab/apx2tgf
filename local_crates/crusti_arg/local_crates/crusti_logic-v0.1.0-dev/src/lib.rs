mod core;
mod languages;
mod queries;
mod sat;
mod transformations;
mod utils;

pub use crate::core::Formula;
pub use crate::core::FormulaNode;
pub use crate::core::FormulaNodeKind;
pub use crate::core::Literal;
pub use crate::core::VarId;

pub use languages::Clause;
pub use languages::CnfFormula;
pub use languages::DnfFormula;
pub use languages::LiteralSetFormula;
pub use languages::NnfFormula;
pub use languages::Term;

pub use queries::Subsumable;

pub use sat::default_sat_solver;
pub use sat::equivalence;
pub use sat::CadicalSatSolver;
pub use sat::ConsistencyCheckResult;
pub use sat::SatSolver;
pub use sat::TseitinEncoder;
pub use sat::MAYBE_TIMEOUT_MSG;

pub use transformations::Conditioning;
pub use transformations::Negation;
pub use transformations::VarReplacement;

pub use utils::MaybeTrivial;
pub use utils::RcMut;
