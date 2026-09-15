/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.IRSProfile
import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.Benchmark.TargetUpper
import ProximityPrize.Benchmark.QuarterRateProfile
import ProximityPrize.Benchmark.QuarterTargetLower
import ProximityPrize.Benchmark.QuarterTargetUpper

import ProximityPrize.Baselines.InitialLower
import ProximityPrize.Baselines.QuarterInitialLower
import ProximityPrize.Baselines.SupportTreeCandidates

/-!
# Binary Proximity Challenge — interleaved-RS reduction thresholds

The public library exposes the half-rate and quarter-rate binary IRS profiles together with lower and upper
certificates for the ABF26 reduction threshold.
-/
