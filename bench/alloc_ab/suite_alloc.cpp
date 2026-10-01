// suite_v2_bench.cpp -- the Phase R-1 benchmark of record harness
// (docs/BENCHMARK_V2_AND_REEVALUATION_PLAN.md §3.4).
//
// Two link targets from the SAME source (per §3.4):
//   -DDSC_ENTRIES_FIVE : links against the five-flagship combined export
//                        (Dsc/checks/Split_Export/dsc_gmp_split_five_export_check.{h,ll}) --
//                        registers all 5 entries (credit/newton/dense/bail/hybrid).
//   (undefined)        : links against the hybrid-only export
//                        (Dsc/checks/Split_Hybrid_Only/dsc_gmp_split_hybrid_only.{h,ll}) --
//                        registers only the hybrid entry, for knob sweeps that must not pay
//                        the 5-way cost.
//
// Per-(case x entry) 600s timeout via fork+pipe+polling waitpid (macOS-safe: no GNU
// `timeout`, no in-process alarm -- a signal landing mid-GMP corrupts state). Min-of-reps
// over COMPLETED reps only; a single timeout marks the whole (case,entry) TIMEOUT.
//
// CSV schema (one row per case x entry): case,family,tier,degree,seed,entry,roots,ms,status
// with status in {OK,TIMEOUT}. Root-count cross-check across entries is ALWAYS ON when more
// than one entry runs on a case: any mismatch is a ⛔ STOP (generator bug or, far worse, a
// soundness bug) -- the harness aborts immediately rather than emitting a wrong row.
#include <signal.h>
#include <sys/wait.h>
#include <unistd.h>
#include <cassert>
#include <cerrno>
#include <chrono>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <gmpxx.h>
#include <iostream>
#include <limits>
#include <map>
#include <regex>
#include <string>
#include <vector>

#include "bench_families.hpp"

// DSC_ENTRIES_PUBLIC (2026-07-31): the CURRENT public export. The two branches below are
// PRE-R-3-RENAME and no longer buildable — `Dsc/checks/Split_Export/` and
// `Dsc/checks/Split_Hybrid_Only/` do not exist, and their entry symbols were renamed to the
// `all_dsc_<name>_main` convention. They are kept, not deleted, so the historical build
// targets that produced the earlier suite-v2 summaries stay readable.
// ⚠️ This is a change to the suite's PLUMBING, not to its case rows — the "suite v2 FREEZE"
// rule (append-only) governs the rows, which are untouched.
#if defined(DSC_ENTRIES_PUBLIC)
extern "C" {
#include "../dsc_adaptive.h"
}
#elif defined(DSC_ENTRIES_FIVE)
extern "C" {
#include "../../checks/Split_Export/dsc_gmp_split_five_export_check.h"
}
#else
extern "C" {
#include "../../checks/Split_Hybrid_Only/dsc_gmp_split_hybrid_only.h"
}
#endif

static_assert(sizeof(gmp_mpz_struct) == sizeof(__mpz_struct), "GMP struct layout mismatch");

static gmp_mpz_struct *as_gmp_ptr(mpz_class &x) {
  return reinterpret_cast<gmp_mpz_struct *>(x.get_mpz_t());
}
static gmp_mpz_struct *as_gmp_ptr_const(const mpz_class &x) {
  return reinterpret_cast<gmp_mpz_struct *>(const_cast<__mpz_struct *>(x.get_mpz_t()));
}

struct GmpPoly {
  std::vector<mpz_class> coeffs;
  std::vector<gmp_mpz_struct *> ptrs;
  explicit GmpPoly(std::vector<mpz_class> c) : coeffs(std::move(c)) {
    while (coeffs.size() > 1 && coeffs.back() == 0) coeffs.pop_back();
    ptrs.reserve(coeffs.size());
    for (const mpz_class &c2 : coeffs) ptrs.push_back(as_gmp_ptr_const(c2));
  }
};

using EntryFn = void (*)(int64_t *, gmp_mpz_struct **, gmp_mpz_struct **, int64_t *, int64_t *,
                          gmp_mpz_struct **, gmp_mpz_struct **, int64_t *, int64_t *, int64_t,
                          int64_t, gmp_mpz_struct **);

struct Entry {
  std::string name;
  EntryFn fn;
};

#if defined(DSC_ENTRIES_PUBLIC)
// ---- powsub ABI adapter ---------------------------------------------------------------
// `all_dsc_powsub_main` does NOT match EntryFn: it takes SIXTEEN parameters, not twelve —
// an extra `out_ok` out-param plus the three knobs (nfloor, hcap, dlt) before `len`
// (dsc_adaptive_contract.h:176). That mismatch, not an oversight, is why no powsub arm ever
// existed here. This adapter supplies the SHIPPED knob values and drops `out_ok`.
//
// 🔴 The knobs are `nfloor = 22, hcap = 32, dlt = 8` — CALIBRATED AND CLOSED, do not sweep
// them here (docs/KNOB_DEFENSIBILITY.md; CLAUDE.md §3.2 track R). `hcap = 32` being a power
// of two is load-bearing for the entry's soundness argument, not a tuning choice.
// `out_ok` is deliberately discarded: it says WHICH CLAIM the intervals carry, not whether
// they are correct — a caller may ignore it and still get correct roots (contract §292).
// The roots this arm returns are compared against the oracle by the same agreement check as
// every other arm, which is the property this suite actually gates on.
static void powsub_entry_adapter(
    int64_t *out_pos_count, gmp_mpz_struct **out_pos_lna, gmp_mpz_struct **out_pos_rnb,
    int64_t *out_pos_k, int64_t *out_neg_count, gmp_mpz_struct **out_neg_lna,
    gmp_mpz_struct **out_neg_rnb, int64_t *out_neg_k, int64_t *out_xs0, int64_t out_cap,
    int64_t len, gmp_mpz_struct **coeff_ptrs) {
  int64_t out_ok = 0;
  all_dsc_powsub_main(out_pos_count, out_pos_lna, out_pos_rnb, out_pos_k,
                      out_neg_count, out_neg_lna, out_neg_rnb, out_neg_k,
                      out_xs0, &out_ok, out_cap,
                      /*nfloor=*/22, /*hcap=*/32, /*dlt=*/8,
                      len, coeff_ptrs);
}
#endif

static std::vector<Entry> all_entries() {
#if defined(DSC_ENTRIES_PUBLIC)
  // R-3 rename map (old check symbol -> current public entry). The ARM LABELS are deliberately
  // UNCHANGED so CSV rows stay directly comparable with the pre-rename suite-v2 summaries:
  //   credit <- all_dsc_carried_split_main_check        -> all_dsc_bisection_main
  //   newton <- all_dsc_carried_split_newton_main_check -> all_dsc_newton_main
  //   dense  <- all_dsc_carried_split_dense_main_check  -> all_dsc_truncate_main
  //   bail   <- all_dsc_carried_split_bail_main_check   -> all_dsc_bail_main
  //   hybrid <- all_dsc_carried_split_hybrid_main_check -> all_dsc_adaptive_main  (THE FLAGSHIP)
  return {
      {"credit", all_dsc_bisection_main},
      {"newton", all_dsc_newton_main},
      {"dense", all_dsc_truncate_main},
      {"bail", all_dsc_bail_main},
      {"hybrid", all_dsc_adaptive_main},
      // powsub/lowdeg added 2026-09-05. Until then this table stopped at the five R-3 entries,
      // so the SHIPPED FLAGSHIP could not be measured by this harness at all — which is why
      // AND-bench's record run has no powsub arm and its flagship figure is a 63-case splice
      // (AND_BENCH.md §5b). See the adapter note above `powsub_entry_adapter`.
      {"powsub", powsub_entry_adapter},
      {"lowdeg", all_dsc_lowdeg_main},
  };
#elif defined(DSC_ENTRIES_FIVE)
  return {
      {"credit", all_dsc_carried_split_main_check},
      {"newton", all_dsc_carried_split_newton_main_check},
      {"dense", all_dsc_carried_split_dense_main_check},
      {"bail", all_dsc_carried_split_bail_main_check},
      {"hybrid", all_dsc_carried_split_hybrid_main_check},
  };
#else
  return {
      {"hybrid", all_dsc_carried_split_hybrid_main_check},
  };
#endif
}

// ---- case table -----------------------------------------------------------------------
struct CaseSpec {
  std::string name;
  std::string family;
  std::string tier;  // "low"|"mid"|"top" (3-point ladder) | "guardrail" (excluded from family
                      // geomean, always runnable) | "spot-check" | "k-grid"/"depth-axis"
                      // (kclu's exempt decision axis) | "ho" (held-out) -- informational
  uint64_t seed;      // 0 if not applicable (deterministic non-random constructions)
  int64_t expected_roots;  // -1 = no closed-form/oracle check yet
  std::string oracle;      // "closed-form" | "sympy" | "cross-flagship-only"
  bench_families::Poly poly;
};

static std::vector<CaseSpec> build_cases() {
  using namespace bench_families;
  std::vector<CaseSpec> cs;
  auto add = [&](std::string name, std::string family, std::string tier, uint64_t seed,
                 int64_t expected, std::string oracle, Poly p) {
    cs.push_back({std::move(name), std::move(family), std::move(tier), seed, expected,
                  std::move(oracle), std::move(p)});
  };

  // ---- KEPT families: uniform 3-point-ladder rule (§3.1/§3.2) ----
  // dense_deg{512,1024,2048}, tau=16 (degree axis)
  add("dense_deg512", "dense", "low", 11, -1, "cross-flagship-only", dense_pattern(512, 16, 11));
  add("dense_deg1024", "dense", "mid", 17, -1, "cross-flagship-only", dense_pattern(1024, 16, 17));
  // REPLACED 2026-07-20 (user-directed, difficulty-target pass: hardest case per family
  // should be >=15s, ideally ~30s -- deg2048 was only 1.4s. deg4096 (~9s) is the safe
  // ceiling found by probing; deg5120 hung for 30+ min on this machine (non-monotonic
  // scaling near this size), so this family is NOT pushed further than deg4096 despite
  // still being short of the 15s target -- documented shortfall, not chased blind.
  add("dense_deg4096", "dense", "top", 17, -1, "cross-flagship-only", dense_pattern(4096, 16, 17));

  // wilkinson_d{80,160,320} (degree axis)
  add("wilkinson_d80", "wilkinson", "low", 0, 80, "closed-form", wilkinson_poly(80));
  add("wilkinson_d160", "wilkinson", "mid", 0, 160, "closed-form", wilkinson_poly(160));
  // REPLACED 2026-07-20 (difficulty-target pass, 15-30s bar): d320 was 0.65s; d800 lands
  // at 28.9s, closed-form oracle unaffected (roots=degree).
  add("wilkinson_d800", "wilkinson", "top", 0, 800, "closed-form", wilkinson_poly(800));

  // chebyshev_d{150,300,600} (degree axis)
  add("chebyshev_d150", "chebyshev", "low", 0, -1, "cross-flagship-only", chebyshev_poly(150));
  add("chebyshev_d300", "chebyshev", "mid", 0, -1, "cross-flagship-only", chebyshev_poly(300));
  // REPLACED 2026-07-20 (difficulty-target pass, 15-30s bar): d600 was 2.1s; d1200 lands
  // at 28.2s.
  add("chebyshev_d1200", "chebyshev", "top", 0, -1, "cross-flagship-only", chebyshev_poly(1200));

  // geom_offgrid_d{130,260,520} (depth-without-cluster falsifier axis)
  add("geom_offgrid_d130", "geom_offgrid", "low", 0, -1, "cross-flagship-only", geometric_offgrid_poly(130));
  add("geom_offgrid_d260", "geom_offgrid", "mid", 0, -1, "cross-flagship-only", geometric_offgrid_poly(260));
  add("geom_offgrid_d520", "geom_offgrid", "top", 0, -1, "cross-flagship-only", geometric_offgrid_poly(520));

  // mig_true_{32_64,64_128,128_256} (tau axis, 3-point ladder)
  add("mig_true_32_64", "mig_true", "low", 0, 4, "closed-form", mignotte_true(32, 64));
  add("mig_true_64_128", "mig_true", "mid", 0, 4, "closed-form", mignotte_true(64, 128));
  // REPLACED 2026-07-20 (difficulty-target pass, 15-30s bar): 128/256 was 11.4s (already
  // close); 144/288 lands at 25.7s, closed-form oracle unaffected (roots=4 by construction).
  add("mig_true_144_288", "mig_true", "top", 0, 4, "closed-form", mignotte_true(144, 288));
  // guardrail: mig_true_96_192 is one of R-2.3's two vcap=1-catastrophe rows -- kept runnable,
  // excluded from the mig_true family geomean.
  add("mig_true_96_192", "mig_true", "guardrail", 0, 4, "closed-form", mignotte_true(96, 192));

  // gauss_{m48_s512,m96_s1024,m96_s2048} (the m x s diagonal as the primary axis)
  add("gauss_m48_s512", "gauss", "low", 12345, -1, "cross-flagship-only", gaussian_clustered_poly(48, 512, 12345));
  add("gauss_m96_s1024", "gauss", "mid", 777, -1, "cross-flagship-only", gaussian_clustered_poly(96, 1024, 777));
  add("gauss_m96_s2048", "gauss", "top", 777, -1, "cross-flagship-only", gaussian_clustered_poly(96, 2048, 777));
  // guardrail: gauss_m48_s1024 is R-2.3's other vcap=1-catastrophe row -- kept runnable,
  // excluded from the gauss family geomean.
  add("gauss_m48_s1024", "gauss", "guardrail", 12345, -1, "cross-flagship-only",
      gaussian_clustered_poly(48, 1024, 12345));

  // nested_68_tau{512,1024,2048} (tau axis) + spot-check nested_132_1024 (n axis)
  add("nested_68_tau512", "nested", "low", 0, -1, "cross-flagship-only", nested_mignotte_poly(68, 512));
  add("nested_68_tau1024", "nested", "mid", 0, -1, "cross-flagship-only", nested_mignotte_poly(68, 1024));
  // REPLACED 2026-07-20 (difficulty-target pass, 15-30s bar): tau2048 was 1.3s; tau16384
  // lands at 23.2s.
  add("nested_68_tau16384", "nested", "top", 0, -1, "cross-flagship-only", nested_mignotte_poly(68, 16384));
  add("nested_132_1024", "nested", "spot-check", 0, -1, "cross-flagship-only", nested_mignotte_poly(132, 1024));

  // ---- NEW family 1: kclu (the load-bearing addition; K is the decision axis, EXEMPT from
  // the 3-point ladder rule -- keeps its full sweep) ----
  for (int K : {2, 4, 6, 8, 12, 16})
    add("kclu_pure_k" + std::to_string(K) + "_tau256", "kclu_pure", "k-grid", 0, K, "closed-form",
        kclu_pure(K, 256));
  for (int T : {128, 512})
    add("kclu_pure_k8_tau" + std::to_string(T), "kclu_pure", "depth-axis", 0, 8, "closed-form",
        kclu_pure(8, T));
  // REPLACED 2026-07-20 (user-directed, explicit replace-not-append authorization -- R-2.x1
  // decay-sweep difficulty review found kclu_pure entirely under 10ms, most under 1ms, the
  // worst-offending family in the suite). The prior tau1024 K in {4,6,8} points (themselves
  // an earlier APPENDED fix for the same problem, see HISTORY) duplicated K values already
  // covered at tau256 without reaching either measurable time OR the pathological K>=12
  // cluster sizes the sigma-fix actually targets -- max was 6.44ms at K=8. Replaced with
  // K in {12,16} at tau1024 (the real blind-spot K values, now at meaningful difficulty)
  // plus one further depth point at tau2048 (K=16) to test whether the fix's value scales
  // with separation depth -- exactly the "hard instance of the exact pathology" the suite
  // was missing. Same closed-form oracle (roots=K), same generator, untouched.
  for (int K : {12, 16})
    add("kclu_pure_k" + std::to_string(K) + "_tau1024", "kclu_pure", "k-grid", 0, K,
        "closed-form", kclu_pure(K, 1024));
  // REPLACED 2026-07-20 (difficulty-target pass, 15-30s bar): k16_tau2048 was 1.1s;
  // k20_tau4096 lands at 12.7s -- short of 15s (k20_tau6144 hung during probing, not
  // chased further), but a real improvement kept as the new ceiling for this row.
  add("kclu_pure_k20_tau4096", "kclu_pure", "k-grid", 0, 20, "closed-form", kclu_pure(20, 4096));

  // kclu_mig: N=128 fixed, K in {2,4} is the exempt decision axis; plus one degree
  // spot-check (n64_k4). REPLACED 2026-07-20 (difficulty-target pass): the K=8 point
  // (n128_k8, was 2.8s) is replaced by n256_k8 (7.8s) -- pushes the N axis instead of K,
  // since K itself scales weakly for this family (K=16 at n128 measured only 36ms in
  // probing); n384_k8 overshot to 62.7s and n512_k8 timed out, so n256 is the safe ceiling,
  // still short of the 15s bar but a real improvement. Root count re-verified (=4, matches
  // the family's existing convention) via a direct probe run before adoption.
  for (int K : {2, 4})
    add("kclu_mig_n128_k" + std::to_string(K) + "_tau256", "kclu_mig", "k-grid", 0, 4, "sympy",
        kclu_mig(128, K, 256));
  add("kclu_mig_n256_k8_tau256", "kclu_mig", "k-grid", 0, 4, "sympy", kclu_mig(256, 8, 256));
  add("kclu_mig_n64_k4_tau256", "kclu_mig", "spot-check", 0, 4, "sympy", kclu_mig(64, 4, 256));

  // ---- NEW family 2: iw/miw (both 3-point ladders) ----
  add("iw_64", "iw", "low", 0, 64, "closed-form", iw_poly(64));
  add("iw_128", "iw", "mid", 0, 128, "closed-form", iw_poly(128));
  // REPLACED 2026-07-20 (difficulty-target pass, 15-30s bar): 256 was 0.16s; 1024 lands
  // at 20.0s, closed-form oracle unaffected (roots=n by construction).
  add("iw_1024", "iw", "top", 0, 1024, "closed-form", iw_poly(1024));
  add("miw_64", "miw", "low", 0, 14, "verified-solver(credit)", miw_poly(64));
  add("miw_128", "miw", "mid", 0, 28, "verified-solver(credit)", miw_poly(128));
  // REPLACED 2026-07-20 (difficulty-target pass, 15-30s bar): 192 was 0.02s; 1536 lands
  // at 23.1s. Switched oracle to cross-flagship-only -- a fixed "verified-solver(credit)"
  // count would need a slow CREDIT-only precompute run (plain bisection is exactly the
  // wrong tool for this family's difficulty), impractical to obtain safely; the harness's
  // built-in cross-entry agreement check (fires on any multi-entry run) verifies this row
  // just as soundly at benchmark-run time, same pattern already used by chebyshev/dense/
  // gauss/geom_offgrid/nested.
  add("miw_1536", "miw", "top", 0, -1, "cross-flagship-only", miw_poly(1536));

  // ---- NEW family 3: sparse/lac (3-point ladders; degree is the axis) ----
  add("sparse_rand_n1024_t12", "sparse_rand", "low", 1024, 2, "verified-solver(credit)", sparse_rand(1024, 12, 1024));
  add("sparse_rand_n2048_t12", "sparse_rand", "mid", 2048, 2, "verified-solver(credit)", sparse_rand(2048, 12, 2048));
  // REPLACED 2026-07-20 (difficulty-target pass, 15-30s bar): n4096 was 4.0s; n6144 lands
  // at 14.5s (n8192 overshot to 43.2s). Switched oracle to cross-flagship-only for the same
  // reason as miw_1536 -- see that comment.
  add("sparse_rand_n6144_t12", "sparse_rand", "top", 6144, -1, "cross-flagship-only", sparse_rand(6144, 12, 6144));
  add("lac_n1024", "lac", "low", 0, 0, "verified-solver(credit)", lac_poly(1024));
  add("lac_n4096", "lac", "mid", 0, 0, "verified-solver(credit)", lac_poly(4096));
  // calibration note: n16384 measured 230s on hybrid (>120s ladder cap) -- shrunk to n8192
  // per §3.1's "trim TOP tiers" rule.
  add("lac_n8192", "lac", "top", 0, 0, "verified-solver(credit)", lac_poly(8192));

  // ---- NEW family 4: res (resultant/CAD) ----
  {
    static const std::map<int, int64_t> res_expected_roots = {{8, 4}, {10, 6}, {12, 4}};
    for (int D : {8, 10, 12}) {
      auto [poly, seed_used] = res_poly(D, static_cast<uint64_t>(1000 + D));
      add("res_d" + std::to_string(D), "res", D <= 8 ? "low" : (D <= 10 ? "mid" : "top"), seed_used,
          res_expected_roots.at(D), "verified-solver(credit)", poly);
    }
  }

  // ---- NEW family 5: mandel ----
  add("mandel_d63", "mandel", "low", 0, 9, "verified-solver(credit)", mandel_poly(6));
  add("mandel_d127", "mandel", "mid", 0, 19, "verified-solver(credit)", mandel_poly(7));
  // REPLACED 2026-07-20 (difficulty-target pass, 15-30s bar): mandel_poly(8) (d255) was
  // 22ms; mandel_poly(11) (degree 2047) lands at 24.2s. Switched oracle to
  // cross-flagship-only for the same reason as miw_1536 -- see that comment.
  add("mandel_d2047", "mandel", "top", 0, -1, "cross-flagship-only", mandel_poly(11));

  // ---- Held-outs (~8, off-grid params; base rows select, held-outs decide) ----
  add("ho_kclu_pure_k6_tau384", "kclu_pure", "ho", 0, 6, "closed-form", kclu_pure(6, 384));
  add("ho_kclu_mig_n96_k4_tau256", "kclu_mig", "ho", 0, 4, "sympy", kclu_mig(96, 4, 256));
  add("ho_iw_96", "iw", "ho", 0, 96, "closed-form", iw_poly(96));
  add("ho_miw_96", "miw", "ho", 0, 22, "verified-solver(credit)", miw_poly(96));
  add("ho_sparse_rand_n3072_t12", "sparse_rand", "ho", 3072, 2, "verified-solver(credit)", sparse_rand(3072, 12, 3072));
  {
    auto [poly, seed_used] = res_poly(9, 1009);
    add("ho_res_d9", "res", "ho", seed_used, 6, "verified-solver(credit)", poly);
  }
  add("ho_nested_100_tau512", "nested", "ho", 0, -1, "cross-flagship-only", nested_mignotte_poly(100, 512));
  add("ho_gauss_m48_s768", "gauss", "ho", 20260712, -1, "cross-flagship-only",
      gaussian_clustered_poly(48, 768, 20260712));

  return cs;
}

// ---- fork-based per-(case,entry) timeout, per §3.4 ------------------------------------
struct RunResult {
  bool timed_out = false;
  double ms = 0.0;
  int64_t roots = -1;
};

static int64_t g_timeout_seconds = 600;  // default per §3.4; --timeout overrides for quick validation passes (never for the benchmark-of-record)

static RunResult run_once(EntryFn fn, const GmpPoly &p, int64_t out_cap) {
  // (uses g_timeout_seconds, set below)
  int fds[2];
  if (pipe(fds) != 0) { perror("pipe"); exit(1); }
  pid_t pid = fork();
  if (pid < 0) { perror("fork"); exit(1); }
  if (pid == 0) {
    // child: run once, write (ms,roots) to the pipe, exit
    close(fds[0]);
    std::vector<mpz_class> pos_l(out_cap), pos_r(out_cap), neg_l(out_cap), neg_r(out_cap);
    std::vector<gmp_mpz_struct *> pos_lp, pos_rp, neg_lp, neg_rp;
    std::vector<int64_t> pos_k(out_cap, -1), neg_k(out_cap, -1);
    for (int64_t i = 0; i < out_cap; ++i) {
      pos_lp.push_back(as_gmp_ptr(pos_l[i]));
      pos_rp.push_back(as_gmp_ptr(pos_r[i]));
      neg_lp.push_back(as_gmp_ptr(neg_l[i]));
      neg_rp.push_back(as_gmp_ptr(neg_r[i]));
    }
    int64_t pos_count = -1, neg_count = -1, xs0 = -1;
    const auto t0 = std::chrono::steady_clock::now();
    fn(&pos_count, pos_lp.data(), pos_rp.data(), pos_k.data(), &neg_count, neg_lp.data(),
       neg_rp.data(), neg_k.data(), &xs0, out_cap, static_cast<int64_t>(p.coeffs.size()),
       const_cast<gmp_mpz_struct **>(p.ptrs.data()));
    const auto t1 = std::chrono::steady_clock::now();
    double ms = std::chrono::duration<double, std::milli>(t1 - t0).count();
    int64_t roots = -1;
    if (pos_count >= 0 && pos_count <= out_cap && neg_count >= 0 && neg_count <= out_cap)
      roots = pos_count + neg_count + (xs0 == 1 ? 1 : 0);
    char buf[64];
    int n = std::snprintf(buf, sizeof buf, "%.6f %lld\n", ms, static_cast<long long>(roots));
    ssize_t written = write(fds[1], buf, static_cast<size_t>(n));
    (void)written;
    close(fds[1]);
    _exit(0);
  }
  // parent
  close(fds[1]);
  const auto deadline = std::chrono::steady_clock::now() + std::chrono::seconds(g_timeout_seconds);
  int status = 0;
  bool done = false;
  while (std::chrono::steady_clock::now() < deadline) {
    pid_t w = waitpid(pid, &status, WNOHANG);
    if (w == pid) { done = true; break; }
    usleep(50 * 1000);
  }
  RunResult r;
  if (!done) {
    kill(pid, SIGKILL);
    waitpid(pid, &status, 0);
    r.timed_out = true;
    close(fds[0]);
    return r;
  }
  char buf[256] = {0};
  ssize_t n = read(fds[0], buf, sizeof(buf) - 1);
  close(fds[0]);
  if (n > 0) {
    double ms;
    long long roots;
    if (std::sscanf(buf, "%lf %lld", &ms, &roots) == 2) {
      r.ms = ms;
      r.roots = roots;
    }
  }
  if (r.roots < 0) r.timed_out = true;  // child crashed or produced no valid output
  return r;
}

// ---- CLI + main ------------------------------------------------------------------------
// --solve-stdin <name> <entry> [reps] [timeout_s]: run ONE compiled-in entry over a polynomial
// read from stdin as one line of comma-separated decimal coefficients (c0,c1,...,cn). Mirrors
// all_roots_vs_competitors_bench.cpp's flag of the same name, and exists for the same reason:
// it lets an external driver (scripts/final-suite-run.py) feed this binary any case from the
// FINAL suite's cached .poly files without porting a single generator.
//
// This is how the FINAL suite reaches the eight "ours" arms (FINAL_BENCHMARK_PLAN.md §4 D5).
// The same source is linked TWICE -- once against the post-vcap-removal export and once against
// the pre-removal one -- because both define the identical five entry symbols and so cannot
// coexist in one binary. Nothing here is export-specific: the entry table does the dispatch.
//
// Output: "<name>,<entry>_roots=<R>,<entry>_ms=<T>" -- the shape the driver's in-process parser
// expects. A timeout prints ms=-1 and roots=-1; the driver's own subprocess cap is the outer
// supervisor, run_once()'s fork deadline the inner one.
static int run_solve_stdin_entry(const std::string &name, const std::string &entry_name,
                                 int reps, int64_t timeout_s) {
  g_timeout_seconds = timeout_s;
  EntryFn fn = nullptr;
  for (const Entry &e : all_entries())
    if (e.name == entry_name) fn = e.fn;
  if (fn == nullptr) {
    std::cerr << "--solve-stdin: unknown entry '" << entry_name << "'; compiled-in:";
    for (const Entry &e : all_entries()) std::cerr << " " << e.name;
    std::cerr << "\n";
    return 2;
  }
  std::string line;
  if (!std::getline(std::cin, line)) {
    std::cerr << "--solve-stdin: no input line on stdin\n";
    return 2;
  }
  std::vector<mpz_class> coeffs;
  size_t pos = 0;
  while (pos <= line.size()) {
    size_t comma = line.find(',', pos);
    std::string tok =
        line.substr(pos, comma == std::string::npos ? std::string::npos : comma - pos);
    if (!tok.empty()) coeffs.emplace_back(tok);
    if (comma == std::string::npos) break;
    pos = comma + 1;
  }
  if (coeffs.empty()) {
    std::cerr << "--solve-stdin: parsed zero coefficients\n";
    return 2;
  }
  const GmpPoly p(std::move(coeffs));
  const int64_t out_cap = static_cast<int64_t>(p.coeffs.size());
  double best = -1.0;
  int64_t roots = -1;
  for (int r = 0; r < reps; ++r) {
    RunResult rr = run_once(fn, p, out_cap);
    if (rr.timed_out) {  // one timeout marks the whole (case,entry), per the §3.4 convention
      std::cout << name << "," << entry_name << "_roots=-1," << entry_name << "_ms=-1\n";
      std::cout.flush();
      return 0;
    }
    if (best < 0 || rr.ms < best) best = rr.ms;  // min over completed reps
    roots = rr.roots;
  }
  std::cout << name << "," << entry_name << "_roots=" << roots << "," << entry_name
            << "_ms=" << best << "\n";
  std::cout.flush();
  return 0;
}

// --solve-stdin-multi <name> <entry> [timeout_s]: SMT-BENCH Phase 2 companion to
// --solve-stdin. Reads MANY polynomials from stdin -- one per line, either dump-format
// ("A\t<deg>\t<c0>,<c1>,..." as written by the nlsat_polydump hook) or a bare comma list --
// and runs the entry once per poly IN-PROCESS (no fork), summing the isolation times and
// root counts. The driver's own subprocess cap is the sole supervisor; a single poly that
// hangs or crashes the entry kills the whole process, which is exactly the per-instance
// TIMEOUT the runner wants. Per-poly fork overhead would dominate the heavy SMT instances
// (40K+ polys), which is why this exists instead of shelling out to --solve-stdin N times.
//
// Output: one "P\t<idx>\t<deg>\t<roots>\t<ms>" line per polynomial (1-based idx in
// input order, deg = poly degree, roots = its count, ms = its isolation time), then
// "<name>,<entry>_roots=<R>,<entry>_ms=<T>,polys=<N>" -- the summary is the verdict the
// Phase 2 runner parses; the P-lines carry the per-poly distribution to
// results/phase2_run2_polys.tsv. A crash prints ms=-1, roots=-1.
// --solve-stdin, plus the poly count. A crash prints ms=-1, roots=-1.
static int run_solve_stdin_multi(const std::string &name, const std::string &entry_name,
                                 int64_t timeout_s) {
  g_timeout_seconds = timeout_s;
  EntryFn fn = nullptr;
  for (const Entry &e : all_entries())
    if (e.name == entry_name) fn = e.fn;
  if (fn == nullptr) {
    std::cerr << "--solve-stdin-multi: unknown entry '" << entry_name << "'\n";
    return 2;
  }
  std::string line;
  double total_ms = 0.0;
  int64_t total_roots = 0;
  unsigned npolys = 0;
  std::string poly_lines;  // per-poly rows "P\t<idx>\t<deg>\t<roots>\t<ms>", emitted once
  while (std::getline(std::cin, line)) {
    if (line.empty()) continue;
    std::string coeff_line = line;
    size_t tab = line.find('\t');
    if (tab != std::string::npos && line.compare(0, 1, "A") == 0) {
      // dump-format: A\t<deg>\t<c0>,<c1>,...
      size_t tab2 = line.find('\t', tab + 1);
      if (tab2 == std::string::npos) continue;
      coeff_line = line.substr(tab2 + 1);
    } else if (tab != std::string::npos) {
      continue;  // B line or malformed -- skip
    }
    std::vector<mpz_class> coeffs;
    size_t pos = 0;
    while (pos <= coeff_line.size()) {
      size_t comma = coeff_line.find(',', pos);
      std::string tok = coeff_line.substr(
          pos, comma == std::string::npos ? std::string::npos : comma - pos);
      if (!tok.empty()) coeffs.emplace_back(tok);
      if (comma == std::string::npos) break;
      pos = comma + 1;
    }
    if (coeffs.empty()) continue;
    const GmpPoly p(std::move(coeffs));
    const int64_t out_cap = static_cast<int64_t>(p.coeffs.size());
    // In-process solve, mirroring run_once()'s child body (no fork: see comment above).
    // ALLOC-IN-TIMER variant (Astra 4.1, 2026-09-27): with DSC_ALLOC_IN_TIMER=1 the clock starts
    // before the output arrays are allocated and initialised, as competitors' result allocation is.
    static const bool alloc_in_timer = std::getenv("DSC_ALLOC_IN_TIMER") != nullptr;
    const auto ta = std::chrono::steady_clock::now();
    std::vector<mpz_class> pos_l(out_cap), pos_r(out_cap), neg_l(out_cap), neg_r(out_cap);
    std::vector<gmp_mpz_struct *> pos_lp, pos_rp, neg_lp, neg_rp;
    std::vector<int64_t> pos_k(out_cap, -1), neg_k(out_cap, -1);
    for (int64_t i = 0; i < out_cap; ++i) {
      pos_lp.push_back(as_gmp_ptr(pos_l[i]));
      pos_rp.push_back(as_gmp_ptr(pos_r[i]));
      neg_lp.push_back(as_gmp_ptr(neg_l[i]));
      neg_rp.push_back(as_gmp_ptr(neg_r[i]));
    }
    int64_t pos_count = -1, neg_count = -1, xs0 = -1;
    // DSC_ALLOC_MIN=1: a caller that allocates minimally per call, inside the timer: one block of
    // 4*cap mpz_t (mpz_init each), one block of 4*cap pointers, one block of 2*cap exponents.
    static const bool alloc_min = std::getenv("DSC_ALLOC_MIN") != nullptr;
    std::chrono::steady_clock::time_point t0, t1;
    if (alloc_min) {
      t0 = std::chrono::steady_clock::now();
      const size_t c = static_cast<size_t>(out_cap);
      __mpz_struct *z = static_cast<__mpz_struct *>(std::malloc(4 * c * sizeof(__mpz_struct)));
      gmp_mpz_struct **ptr = static_cast<gmp_mpz_struct **>(std::malloc(4 * c * sizeof(void *)));
      int64_t *kk = static_cast<int64_t *>(std::malloc(2 * c * sizeof(int64_t)));
      for (size_t i = 0; i < 4 * c; ++i) { mpz_init(&z[i]); ptr[i] = reinterpret_cast<gmp_mpz_struct *>(&z[i]); }
      fn(&pos_count, ptr, ptr + c, kk, &neg_count, ptr + 2 * c, ptr + 3 * c, kk + c, &xs0, out_cap,
         static_cast<int64_t>(p.coeffs.size()), const_cast<gmp_mpz_struct **>(p.ptrs.data()));
      t1 = std::chrono::steady_clock::now();
      for (size_t i = 0; i < 4 * c; ++i) mpz_clear(&z[i]);
      std::free(z); std::free(ptr); std::free(kk);
    } else {
    t0 = alloc_in_timer ? ta : std::chrono::steady_clock::now();
    fn(&pos_count, pos_lp.data(), pos_rp.data(), pos_k.data(), &neg_count, neg_lp.data(),
       neg_rp.data(), neg_k.data(), &xs0, out_cap, static_cast<int64_t>(p.coeffs.size()),
       const_cast<gmp_mpz_struct **>(p.ptrs.data()));
    t1 = std::chrono::steady_clock::now();
    }
    double ms = std::chrono::duration<double, std::milli>(t1 - t0).count();
    if (pos_count < 0 || pos_count > out_cap || neg_count < 0 || neg_count > out_cap) {
      std::cout << poly_lines << name << "," << entry_name << "_roots=-1," << entry_name
                << "_ms=-1,polys=" << npolys << "\n";
      std::cout.flush();
      return 0;
    }
    poly_lines += "P\t" + std::to_string(npolys + 1) + "\t" +
                  std::to_string(static_cast<int64_t>(p.coeffs.size()) - 1) + "\t" +
                  std::to_string(pos_count + neg_count + (xs0 == 1 ? 1 : 0)) + "\t" +
                  std::to_string(ms) + "\n";
    total_ms += ms;
    total_roots += pos_count + neg_count + (xs0 == 1 ? 1 : 0);
    ++npolys;
  }
  if (npolys == 0) {
    std::cerr << "--solve-stdin-multi: no polynomials parsed\n";
    return 2;
  }
  std::cout << poly_lines << name << "," << entry_name << "_roots=" << total_roots
            << "," << entry_name << "_ms=" << total_ms << ",polys=" << npolys << "\n";
  std::cout.flush();
  return 0;
}

int main(int argc, char **argv) {
  // --solve-stdin-multi <name> <entry> [timeout_s]: see run_solve_stdin_multi() above.
  if (argc > 1 && std::string(argv[1]) == "--solve-stdin-multi") {
    if (argc < 4) {
      std::cerr << "usage: --solve-stdin-multi <name> <entry> [timeout_s] < poly_lines\n";
      return 2;
    }
    const int64_t tmo = argc > 4 ? std::atoll(argv[4]) : 150;
    return run_solve_stdin_multi(argv[2], argv[3], tmo);
  }

  // --solve-stdin <name> <entry> [reps] [timeout_s]: see run_solve_stdin_entry() above.
  if (argc > 1 && std::string(argv[1]) == "--solve-stdin") {
    if (argc < 4) {
      std::cerr << "usage: --solve-stdin <name> <entry> [reps] [timeout_s] < coeffs_line\n";
      return 2;
    }
    const int reps = argc > 4 ? std::atoi(argv[4]) : 3;
    const int64_t tmo = argc > 5 ? std::atoll(argv[5]) : 600;
    return run_solve_stdin_entry(argv[2], argv[3], reps, tmo);
  }

  std::vector<std::string> wanted_entries;  // empty = all compiled-in entries
  std::string case_regex;
  int reps = 3;
  bool calibrate = false;
  bool dump_coeffs = false;

  for (int i = 1; i < argc; ++i) {
    std::string a = argv[i];
    if (a == "--entries" && i + 1 < argc) {
      std::string v = argv[++i];
      if (v != "all") {
        size_t pos = 0;
        while (pos < v.size()) {
          size_t comma = v.find(',', pos);
          wanted_entries.push_back(v.substr(pos, comma == std::string::npos ? comma : comma - pos));
          if (comma == std::string::npos) break;
          pos = comma + 1;
        }
      }
    } else if (a == "--cases" && i + 1 < argc) {
      case_regex = argv[++i];
    } else if (a == "--reps" && i + 1 < argc) {
      reps = std::stoi(argv[++i]);
    } else if (a == "--calibrate") {
      calibrate = true;
      reps = 1;
      wanted_entries = {"hybrid"};
    } else if (a == "--dump-coeffs") {
      dump_coeffs = true;
    } else if (a == "--timeout" && i + 1 < argc) {
      g_timeout_seconds = std::stoll(argv[++i]);
    }
  }

  if (dump_coeffs) {
    // oracle-pass helper: print raw coefficients per case (no solver invocation at all), for
    // an external script (e.g. a sympy pass) to compute exact root counts.
    std::vector<CaseSpec> cases = build_cases();
    std::regex re;
    bool has_regex = !case_regex.empty();
    if (has_regex) re = std::regex(case_regex);
    for (const auto &cs : cases) {
      if (has_regex && !std::regex_search(cs.name, re)) continue;
      std::cout << cs.name;
      for (const auto &c : cs.poly) std::cout << "," << c;
      std::cout << "\n";
    }
    return 0;
  }

  std::vector<Entry> entries = all_entries();
  if (!wanted_entries.empty()) {
    std::vector<Entry> filtered;
    for (auto &e : entries)
      if (std::find(wanted_entries.begin(), wanted_entries.end(), e.name) != wanted_entries.end())
        filtered.push_back(e);
    entries = filtered;
  }
  if (entries.empty()) {
    std::cerr << "no matching entries for --entries filter (this binary provides: ";
    for (auto &e : all_entries()) std::cerr << e.name << " ";
    std::cerr << ")\n";
    return 1;
  }

  std::vector<CaseSpec> cases = build_cases();
  std::regex re;
  bool has_regex = !case_regex.empty();
  if (has_regex) re = std::regex(case_regex);

  if (!calibrate) std::cout << "case,family,tier,degree,seed,entry,roots,ms,status\n";
  else std::cout << "case,family,tier,degree,ms\n";
  std::cout.flush();

  for (const auto &cs : cases) {
    if (has_regex && !std::regex_search(cs.name, re)) continue;
    GmpPoly p(cs.poly);
    int64_t out_cap = static_cast<int64_t>(p.coeffs.size());
    int64_t degree = static_cast<int64_t>(p.coeffs.size()) - 1;

    if (calibrate) {
      RunResult r = run_once(entries[0].fn, p, out_cap);
      std::cout << cs.name << "," << cs.family << "," << cs.tier << "," << degree << ","
                << (r.timed_out ? -1.0 : r.ms) << "\n";
      std::cout.flush();
      continue;
    }

    int64_t agreed_roots = -2;  // -2 = not yet set
    for (const auto &e : entries) {
      double best_ms = std::numeric_limits<double>::infinity();
      int64_t roots = -1;
      bool any_timeout = false;
      for (int r = 0; r < reps; ++r) {
        RunResult rr = run_once(e.fn, p, out_cap);
        if (rr.timed_out) { any_timeout = true; continue; }
        if (rr.ms < best_ms) { best_ms = rr.ms; roots = rr.roots; }
      }
      std::string status = any_timeout ? "TIMEOUT" : "OK";
      if (status == "TIMEOUT" && roots < 0) { best_ms = static_cast<double>(g_timeout_seconds) * 1000.0; }

      // layer 1 (always-on): cross-entry root-count agreement, when >1 entry runs and this
      // entry actually completed at least one rep
      if (roots >= 0) {
        if (agreed_roots == -2) {
          agreed_roots = roots;
        } else if (agreed_roots != roots) {
          std::cerr << "\n*** ROOT-COUNT MISMATCH on case '" << cs.name << "': entry '" << e.name
                    << "' got " << roots << ", expected " << agreed_roots
                    << " (from an earlier entry on the same case). Generator bug or a soundness"
                    << " bug -- STOPPING per standing law. ***\n";
          return 2;
        }
      }
      // layer 2/3 (closed-form / sympy oracle): only checked once expected_roots is populated
      if (cs.expected_roots >= 0 && roots >= 0 && roots != cs.expected_roots) {
        std::cerr << "\n*** ROOT-COUNT MISMATCH on case '" << cs.name << "': entry '" << e.name
                  << "' got " << roots << ", oracle (" << cs.oracle << ") expects "
                  << cs.expected_roots << ". STOPPING per standing law. ***\n";
        return 2;
      }

      std::cout << cs.name << "," << cs.family << "," << cs.tier << "," << degree << ","
                << cs.seed << "," << e.name << "," << roots << "," << best_ms << "," << status
                << "\n";
      std::cout.flush();
    }
  }
  return 0;
}
