import json
from z3 import Int, Solver, Distinct, And, Or, Abs, sat

# Define entities
houses = [1, 2, 3, 4]
names = ["Arnold", "Eric", "Peter", "Alice"]
occupations = ["doctor", "engineer", "artist", "teacher"]

# Z3 variables: position (house number) for each name and each occupation
pos_name = {n: Int(f"pos_name_{n}") for n in names}
pos_occ = {o: Int(f"pos_occ_{o}") for o in occupations}

s = Solver()

# Domain constraints: positions are between 1 and 4
for v in list(pos_name.values()) + list(pos_occ.values()):
    s.add(And(v >= 1, v <= 4))

# Uniqueness constraints within each category
s.add(Distinct(*pos_name.values()))
s.add(Distinct(*pos_occ.values()))

# Clues:
# 1. There are two houses between Eric and Peter -> positions differ by 3 (e.g., 1 and 4)
s.add(Abs(pos_name["Eric"] - pos_name["Peter"]) == 3)

# 2. The person who is a teacher is Peter
s.add(pos_occ["teacher"] == pos_name["Peter"])

# 3. Peter is not in the first house
s.add(pos_name["Peter"] != 1)

# 4. There is one house between the person who is a doctor and Alice -> positions differ by 2
s.add(Abs(pos_occ["doctor"] - pos_name["Alice"]) == 2)

# 5. The person who is an artist is Alice
s.add(pos_occ["artist"] == pos_name["Alice"])

# Solve
if s.check() != sat:
    raise RuntimeError("No solution found")

m = s.model()

# Invert mappings to get per-house assignments
name_by_house = {m[pos_name[n]].as_long(): n for n in names}
occ_by_house = {m[pos_occ[o]].as_long(): o for o in occupations}

# Build the required JSON structure
solution = {
    "solution": {
        "header": ["House", "Name", "Occupation"],
        "rows": [
            [str(h), name_by_house[h], occ_by_house[h]] for h in houses
        ]
    }
}

print(json.dumps(solution, ensure_ascii=False))