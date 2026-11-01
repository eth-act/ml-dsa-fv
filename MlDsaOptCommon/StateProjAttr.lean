import Lean
set_option warningAsError true
/-! The simp set `state_proj` (see `MlDsaOptCommon.StateProj`); registered in its
own module because an attribute cannot be used in the module that declares it. -/

/-- Field projections of state literals, as proof-producing rewrites. -/
register_simp_attr state_proj
