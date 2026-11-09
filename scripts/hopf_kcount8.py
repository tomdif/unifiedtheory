import collections
src = open("pi4_first_prediction.py").read().split("# ---------------- per-parent pi/4 machinery")[0]
g = {"__name__": "engine"}; exec(compile(src, "engine", "exec"), g)
c = collections.Counter(len(g["children"][p]) for p in g["parents"])
print("depth-8 tree (2450 parents): K distribution", dict(sorted(c.items())))
print("binary parents:", [(p, g["children"][p]) for p in g["parents"] if len(g["children"][p]) == 2])
