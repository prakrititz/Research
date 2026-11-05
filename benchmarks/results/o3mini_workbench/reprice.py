"""Re-price tonight's runs at list prices (the tracker charged unknown models 2.50/10.00 per million tokens)."""
import glob, os, re
S = os.path.dirname(os.path.abspath(__file__))
USAGE = re.compile(r"\[Usage: (\d+) prompt \+ (\d+) completion tokens \| Call: \$([0-9.]+)")
old = new = 0.0
for f in glob.glob(os.path.join(S, "ladder", "*.log")) + glob.glob(os.path.join(S, "ab", "*.log")):
    for p, c, cost in USAGE.findall(open(f, encoding="utf8", errors="replace").read()):
        old += float(cost)
        new += int(p) * 0.75e-6 + int(c) * 4.50e-6
print(f"tracker said ${old:.2f}; at gpt-5.4-mini list price ${new:.2f} (the few gpt-5.4 proof calls are priced as mini here)")
