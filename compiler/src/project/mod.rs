//! Multi-file Napitia projects: manifests, module discovery, the
//! module dependency graph, and cross-module import resolution
//! (`rfcs/0006`).

pub mod manifest;

pub(crate) mod codes {
    pub const INVALID_MANIFEST: &str = "M0001";
    pub const INVALID_PROJECT_PATH: &str = "M0002";
    pub const INVALID_IMPORT_PATH: &str = "M0003";
    pub const MODULE_NOT_FOUND: &str = "M0004";
    pub const ITEM_NOT_FOUND: &str = "M0005";
    pub const ITEM_PRIVATE: &str = "M0006";
    pub const DUPLICATE_IMPORT: &str = "M0007";
    pub const IMPORT_CYCLE: &str = "M0008";
    pub const MODULE_PATH_COLLISION: &str = "M0009";
    pub const INVALID_ENTRY: &str = "M0010";
    pub const INACCESSIBLE_FIELD: &str = "M0011";
    pub const PRIVATE_TYPE_LEAKED: &str = "M0012";
}
