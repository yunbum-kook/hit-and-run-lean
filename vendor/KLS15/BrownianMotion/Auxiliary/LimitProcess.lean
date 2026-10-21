/-
Copyright (c) 2026 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import BrownianMotion.Auxiliary.Indistinguishable
public import KLS15Compat.Probability.Process.LimitProcess

public section

open MeasureTheory Filter
open scoped Topology

/- The limit-process declarations of this auxiliary module have been upstreamed
   into KLS15Compat.Probability.Process.LimitProcess; re-export the checked versions. -/
