#!/usr/bin/env python3
"""Bounded sample-certificate generation and independent replay for six inputs.

The finite search mirrors the attributed Lean framework in
https://github.com/open-goat/pequalnp-proofs/pull/17808 .
A generated rejection remains computational evidence until Lean checks it.
"""
from __future__ import annotations

import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import itertools
import json
import math
from pathlib import Path
import random
import re
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ENGINE = HERE / "sampled_binary_search"
SUPPORT = HERE / "SampledBinaryLowerSupport.lean"
MASK = (1 << 64) - 1
HALF = (1 << 32) - 1
GOAL = HALF << 32
SOURCE = "https://github.com/open-goat/pequalnp-proofs/pull/17808"


def number(s):
    return int(s, 0) if isinstance(s, str) else int(s)


def read_json(path):
    return json.loads(Path(path).read_text())


def write_json(path, obj):
    p = Path(path)
    p.parent.mkdir(parents=True, exist_ok=True)
    temp = p.with_name(p.name + ".tmp")
    temp.write_text(json.dumps(obj, indent=2) + "\n")
    temp.replace(p)


def analyze(table):
    if not 0 <= table <= MASK:
        raise ValueError("truth table must be an unsigned 64-bit integer")
    pos = [x for x in range(64) if (table >> x) & 1]
    neg = [x for x in range(64) if not (table >> x) & 1]
    monotone = all(not (table >> x) & 1 or (table >> (x | (1 << i))) & 1
                   for x in range(64) for i in range(6))
    essential = [i for i in range(6) if any(((table >> x) ^ (table >> (x ^ (1 << i)))) & 1
                                          for x in range(64))]
    minpos = [x for x in pos if all(not (x >> i) & 1 or not (table >> (x ^ (1 << i))) & 1 for i in range(6))]
    maxneg = [x for x in neg if all((x >> i) & 1 or (table >> (x | (1 << i))) & 1 for i in range(6))]
    return {"positive": pos, "negative": neg, "monotone": monotone,
            "essential_inputs": essential, "minimal_true": minpos, "maximal_false": maxneg}


def encode_pairs(positive, negative):
    if len(positive) != 32 or len(negative) != 32:
        raise ValueError("exactly 32 positive and 32 negative sample rows required")
    return [sum(((x >> i) & 1) << k for k, x in enumerate(positive + negative)) for i in range(6)]


def validate_samples(table, rows):
    if len(rows) != 6 or any(not 0 <= x <= MASK for x in rows):
        raise ValueError("six unsigned 64-bit masks required")
    if len(set(rows)) != 6:
        raise ValueError("input masks must be pairwise distinct for the Lean bridge")
    assignments = [sum(((rows[i] >> k) & 1) << i for i in range(6)) for k in range(64)]
    bad = [k for k, x in enumerate(assignments) if ((table >> x) & 1) != (k < 32)]
    if bad:
        raise ValueError(f"sample labels disagree with the function at positions {bad}")
    return {"positive_samples": assignments[:32], "negative_samples": assignments[32:],
            "input_masks_distinct": True, "all_64_sample_labels_correct": True}


def certificate_inputs(data):
    table = number(data["truth_table"])
    rows = list(map(number, data["rows"]))
    bound = data["binary_bound"]
    if type(bound) is not int or not 0 <= bound <= 10:
        raise ValueError("certificate binary_bound must be an integer between 0 and 10")
    if not 0 <= table <= MASK:
        raise ValueError("certificate truth table is outside 64 bits")
    validate_samples(table, rows)
    return table, rows, bound


def make_samples(table, rng, strategy):
    a = analyze(table)
    if not a["monotone"] or not a["positive"] or not a["negative"]:
        raise ValueError("method expects a nonconstant monotone six-input function")
    boundary = [(x | (1 << i), x) for i in range(6) for x in a["negative"]
                if not (x >> i) & 1 and (table >> (x | (1 << i))) & 1]
    pairs = []
    for i in a["essential_inputs"]:
        choices = [(p, n) for p, n in boundary if p ^ n == 1 << i]
        pairs.append(rng.choice(choices))
    cross = list(itertools.product(a["minimal_true"], a["maximal_false"]))
    rng.shuffle(boundary)
    rng.shuffle(cross)
    if strategy % 3 == 0:
        candidates = boundary + cross
    elif strategy % 3 == 1:
        candidates = [v for p in itertools.zip_longest(boundary, cross) for v in p if v is not None]
    else:
        candidates = cross + boundary
    for pair in candidates:
        if len(pairs) == 32:
            break
        if pair not in pairs:
            pairs.append(pair)
    while len(pairs) < 32:
        pairs.append((rng.choice(a["positive"]), rng.choice(a["negative"])))
    rng.shuffle(pairs)
    positive, negative = map(list, zip(*pairs))
    rows = encode_pairs(positive, negative)
    validate_samples(table, rows)
    return rows


def validate_witness(table, obj):
    gates = obj.get("gates", obj.get("witness_gates"))
    output = obj.get("output", obj.get("witness_output"))
    if gates is None or output is None:
        raise ValueError("witness JSON needs gates and output")
    normal = []
    for k, gate in enumerate(gates):
        if isinstance(gate, dict):
            op, ins = gate["op"], gate["inputs"]
        else:
            op, *ins = gate
        op = op.lower().lstrip(".")
        if op not in ("and", "or") or len(ins) > 2 or any(not isinstance(i, int) or not 0 <= i < 6+k for i in ins):
            raise ValueError(f"invalid AO gate {k}: {gate}")
        normal.append({"op": op, "inputs": ins})
    if not isinstance(output, int) or not 0 <= output < 6+len(normal):
        raise ValueError("invalid output wire")
    actual = 0
    for x in range(64):
        wires = [bool((x >> i) & 1) for i in range(6)]
        for g in normal:
            vals = [wires[i] for i in g["inputs"]]
            wires.append(all(vals) if g["op"] == "and" else any(vals))
        if wires[output]:
            actual |= 1 << x
    if actual != table:
        raise ValueError("AO witness does not compute the given truth table")
    return {"gates": normal, "output": output, "gate_count": len(normal), "all_64_inputs_correct": True}


def cpp_replay(rows, bound, seconds, node_limit):
    if not ENGINE.exists():
        raise ValueError(f"compile engine first: g++ -O3 -std=c++17 {ENGINE}.cpp -o {ENGINE}")
    argv = [str(ENGINE), str(bound), str(min(60, seconds)), str(node_limit), *map(hex, rows)]
    proc = subprocess.Popen(argv, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    try:
        out, err = proc.communicate(timeout=min(60, seconds)+5)
    except BaseException:
        proc.kill()
        proc.communicate()
        raise
    if proc.returncode:
        raise ValueError(f"engine exited {proc.returncode}: {err.strip()}")
    return json.loads(out)


class BudgetEnd(Exception):
    pass


def python_replay(rows, bound, seconds, node_limit):
    """Literal list-order replay, independent of the C++ permutation cache."""
    begin = time.monotonic()
    nodes = 0

    def sep(w):
        return ((w >> 32) ^ w) & HALF

    def cuts(ws):
        v = 0
        for w in ws:
            v |= sep(w)
        return v

    @lru_cache(maxsize=100000)
    def opt(fuel, extra, ws):
        nonlocal nodes
        nodes += 1
        if nodes >= node_limit:
            raise BudgetEnd("node_limit")
        if nodes % 256 == 0 and time.monotonic()-begin >= seconds:
            raise BudgetEnd("time_limit")
        if ws in [(GOAL,), (MASK ^ GOAL,)]:
            return True
        if not fuel:
            return False
        for i, j in itertools.combinations(range(len(ws)), 2):
            a, b = ws[i], ws[j]
            rest = ws[:i] + ws[i+1:j] + ws[j+1:]
            base = cuts(rest)
            for w in [a & b, a | b, a & (MASK ^ b), b & (MASK ^ a)]:
                v = sep(w) | base
                if v == HALF and opt(fuel-1, extra, (w,)+rest):
                    return True
                if extra and ((v | sep(a) == HALF and opt(fuel-1, extra-1, (w,a)+rest))
                              or (v | sep(b) == HALF and opt(fuel-1, extra-1, (w,b)+rest))):
                    return True
                if extra >= 2 and v | sep(a) | sep(b) == HALF and opt(fuel-1, extra-2, (w,a,b)+rest):
                    return True
        return False
    try:
        feasible = False
        for flags in range(64):
            if time.monotonic()-begin >= seconds:
                raise BudgetEnd("time_limit")
            ws = tuple(w for i, w in enumerate(rows) if (flags >> i) & 1)
            if len(ws) <= bound+1 and cuts(ws) == HALF and opt(bound, bound+1-len(ws), ws):
                feasible = True
                break
        status = "sample_feasible" if feasible else "exhaustive_rejection"
    except BudgetEnd as exc:
        status = str(exc)
    return {"status": status, "bound": bound, "elapsed_seconds": time.monotonic()-begin,
            "nodes": nodes, "cache": opt.cache_info()._asdict(), "implementation": "literal_python_list_order"}


def generate(args):
    table = number(args.table)
    info = analyze(table)
    witness = validate_witness(table, read_json(args.witness)) if args.witness else None
    bound = args.bound
    if bound is None:
        if witness is None or witness["gate_count"] < 2:
            raise ValueError("supply --bound or an AO witness with at least two gates")
        bound = witness["gate_count"]-2
    if not 0 <= bound <= 10:
        raise ValueError("bound must be between 0 and 10")
    if witness and witness["gate_count"] > bound+2:
        raise ValueError("this lower bound would not support the supplied AO witness")
    begin = time.monotonic()
    records = []
    rng = random.Random(args.seed)
    rows = None
    status = "no_rejection_certificate"
    for attempt in range(args.attempts):
        remaining = args.seconds-(time.monotonic()-begin)
        if remaining <= 0:
            break
        rows = make_samples(table, rng, attempt)
        result = cpp_replay(rows, bound, min(args.attempt_seconds, remaining), args.nodes)
        records.append(result)
        print(json.dumps({"attempt": attempt+1, **result}), file=sys.stderr, flush=True)
        if result["status"] == "exhaustive_rejection":
            status = "exhaustive_rejection"
            break
    result = {"schema": "sampled-binary-lower-v1", "framework_source": SOURCE,
              "status": status, "truth_table": hex(table), "binary_bound": bound,
              "rows": list(map(hex, rows)) if rows else None, "analysis": info,
              "sample_validation": validate_samples(table, rows) if rows else None,
              "attempts": records, "seed": args.seed, "elapsed_seconds": time.monotonic()-begin,
              "kernel_checked": False,
              "meaning": "rejection excludes this many binary gates with NOT free; sample_feasible is not a counterexample for the full function"}
    if witness:
        result["ao_witness"] = witness
    write_json(args.output, result)
    print(json.dumps({"status": status, "output": str(Path(args.output).resolve()), "bound": bound,
                      "attempts": len(records), "kernel_checked": False}))


def replay(args):
    data = read_json(args.certificate)
    table, rows, bound = certificate_inputs(data)
    labels = validate_samples(table, rows)
    result = {"sample_validation": labels, "kernel_checked": False}
    for name, fn in [("cpp", cpp_replay), ("python", python_replay)]:
        if args.engine in (name, "both"):
            result[name] = fn(rows, bound, args.seconds, args.nodes)
    exact = [v["status"] for k,v in result.items() if k in ("cpp", "python") and v["status"] in ("exhaustive_rejection", "sample_feasible")]
    if len(set(exact)) > 1:
        raise AssertionError("independent search implementations disagree")
    if args.output:
        write_json(args.output, result)
    print(json.dumps(result, indent=2))


def emit(args):
    data = read_json(args.certificate)
    if data["status"] != "exhaustive_rejection":
        raise ValueError("emit requires an exhaustive rejection, not timeout or sample feasibility")
    table, rows, n = certificate_inputs(data)
    validate_samples(table, rows)
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*", args.namespace):
        raise ValueError("invalid Lean namespace")
    body = SUPPORT.read_text()
    ns = "PEqualNP.Methods.SampledBinaryLower"
    if f"end {ns}" not in body:
        raise ValueError("support template malformed")
    body = body.rsplit(f"end {ns}", 1)[0].replace(f"namespace {ns}", f"namespace {args.namespace}")
    body += f'''\ndef certificateTable : ℕ := {hex(table)}
def certificateTarget (x : Fin 6 → Bool) : Bool :=
  certificateTable.testBit (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def certificateRows : List W := [{", ".join(map(hex, rows))}]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateReject : search {n} certificateRows = false := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateLabels : ∀ k : Fin 64,
    certificateTarget (fun i => (certificateRows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel
theorem certificateBinaryLower (gs : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = certificateTarget x) :
    {n} < binaryCost gs :=
  bound_from_search {n} certificateTarget certificateRows rfl (by decide)
    certificateReject certificateLabels gs o hg he
'''
    if data.get("ao_witness"):
        w = validate_witness(table, data["ao_witness"])
        if w["gate_count"] > n+2:
            raise ValueError("AO witness too large for transfer")
        gs = ", ".join("⟨."+g["op"]+", ["+", ".join(map(str,g["inputs"]))+"]⟩" for g in w["gates"])
        body += f'''\ndef certificateWitness : Circuit := ⟨[{gs}], {w["output"]}⟩
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem certificateWitnessCorrect : ∀ x : Fin 6 → Bool,
    certificateWitness.eval (List.ofFn x) = certificateTarget x := by decide +kernel
theorem certificateTransfer : ∀ s, HasCircuitSize 6 certificateTarget s →
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
      ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = certificateTarget x :=
  transfer_from_search {n} certificateTarget certificateRows rfl (by decide)
    certificateReject certificateLabels certificateWitness
    (by simp [Monotone2, certificateWitness]) (by decide) certificateWitnessCorrect
'''
    body += f"\nend {args.namespace}\n"
    out = Path(args.output)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(body)
    print(json.dumps({"output": str(out.resolve()), "bytes": len(body.encode()), "kernel_checked": False,
                      "source_certificate_sha256": hashlib.sha256(Path(args.certificate).read_bytes()).hexdigest()}))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest="command", required=True)
    g = sub.add_parser("generate")
    g.add_argument("--table", required=True)
    g.add_argument("--bound", type=int)
    g.add_argument("--witness")
    g.add_argument("--output", required=True)
    g.add_argument("--seconds", type=float, default=20)
    g.add_argument("--attempt-seconds", type=float, default=3)
    g.add_argument("--attempts", type=int, default=8)
    g.add_argument("--nodes", type=int, default=2000000)
    g.add_argument("--seed", type=int, default=0)
    g.set_defaults(action=generate)
    r = sub.add_parser("replay")
    r.add_argument("certificate")
    r.add_argument("--engine", choices=["cpp","python","both"], default="python")
    r.add_argument("--seconds", type=float, default=10)
    r.add_argument("--nodes", type=int, default=1000000)
    r.add_argument("--output")
    r.set_defaults(action=replay)
    e = sub.add_parser("emit-lean")
    e.add_argument("certificate")
    e.add_argument("--namespace", default="PEqualNP.Generated.SampledLower")
    e.add_argument("--output", required=True)
    e.set_defaults(action=emit)
    args = p.parse_args()
    for name in ["seconds", "attempt_seconds"]:
        if hasattr(args, name):
            v = getattr(args, name)
            if not math.isfinite(v) or not 0 < v <= 60:
                p.error(f"--{name.replace('_','-')} must be in (0,60]")
    if hasattr(args,"nodes") and args.nodes <= 0:
        p.error("--nodes must be positive")
    if hasattr(args,"attempts") and not 1 <= args.attempts <= 64:
        p.error("--attempts must be between1 and64")
    try:
        args.action(args)
    except (ValueError, OSError) as exc:
        p.error(str(exc))


if __name__ == "__main__":
    main()
