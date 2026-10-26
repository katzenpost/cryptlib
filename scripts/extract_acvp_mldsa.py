"""Extract ML-DSA-65 from NIST ACVP-Server's internalProjection.json files
(gen-val/json-files/ML-DSA-{keyGen,sigGen,sigVer}-FIPS204) into testdata/mldsa65_*.json.
Pre-hash (HashML-DSA) groups are left out."""
import json, sys

keygen_src, siggen_src, sigver_src, outdir = sys.argv[1:5]
ps = "ML-DSA-65"
src = "NIST ACVP-Server (github.com/usnistgov/ACVP-Server), gen-val/json-files/"

def write(name, generator, desc, vectors):
    doc = {"format_version": 1, "generator": generator, "primitive": f"mldsa65_{name}",
           "description": desc, "vectors": vectors}
    with open(f"{outdir}/mldsa65_{name}.json", "w") as f:
        json.dump(doc, f, indent=2)
        f.write("\n")

def mode(g):
    if g["signatureInterface"] == "external":
        return "external"
    return "mu" if g["externalMu"] else "internal"

kg = json.load(open(keygen_src))
write("keygen", src + f"ML-DSA-keyGen-FIPS204/internalProjection.json, {ps} test group only",
      f"Official NIST ACVP known-answer vectors for {ps} key generation (FIPS 204 Algorithm 6): seed -> pk, sk.",
      [{"name": f"tc{t['tcId']}", "seed_hex": t["seed"], "pk_hex": t["pk"], "sk_hex": t["sk"]}
       for g in kg["testGroups"] if g["parameterSet"] == ps for t in g["tests"]])

sg = json.load(open(siggen_src))
vs = []
for g in sg["testGroups"]:
    if g["parameterSet"] != ps or g["preHash"] == "preHash": continue
    for t in g["tests"]:
        v = {"name": f"tc{t['tcId']}-{mode(g)}-{'det' if g['deterministic'] else 'hedged'}",
             "mode": mode(g), "sk_hex": t["sk"], "rnd_hex": t.get("rnd", "00" * 32),
             "signature_hex": t["signature"]}
        if mode(g) == "mu": v["mu_hex"] = t["mu"]
        else: v["message_hex"] = t["message"]
        if mode(g) == "external": v["context_hex"] = t["context"]
        vs.append(v)
write("siggen", src + f"ML-DSA-sigGen-FIPS204/internalProjection.json, {ps} pure and internal test groups",
      f"Official NIST ACVP known-answer vectors for {ps} signing (FIPS 204 Algorithms 2 and 7), deterministic and hedged, through the external interface (M' = 0 || |ctx| || ctx || M), the internal one (M' given), and with mu given directly.",
      vs)

sv = json.load(open(sigver_src))
vs = []
for g in sv["testGroups"]:
    if g["parameterSet"] != ps or g["preHash"] == "preHash" or mode(g) == "mu": continue
    for t in g["tests"]:
        v = {"name": f"tc{t['tcId']}-{mode(g)}-{t['reason'].replace(' ', '_')}", "mode": mode(g),
             "pk_hex": t["pk"], "message_hex": t["message"], "signature_hex": t["signature"],
             "want_pass": t["testPassed"], "reason": t["reason"]}
        if mode(g) == "external": v["context_hex"] = t["context"]
        vs.append(v)
write("sigver", src + f"ML-DSA-sigVer-FIPS204/internalProjection.json, {ps} pure and internal test groups",
      f"Official NIST ACVP known-answer vectors for {ps} verification (FIPS 204 Algorithms 3 and 8), including signatures that must be rejected.",
      vs)
