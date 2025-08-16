# Solve the logic puzzle with Z3 and print the required JSON
from z3 import Solver, Int, Distinct, And, Or, Implies, sat
import json

# Enumerations
Names = ["Peter", "Alice", "Eric", "Bob", "Arnold"]
Birthdays = ["april", "feb", "mar", "jan", "sept"]
Cigars = ["pall mall", "prince", "dunhill", "blends", "blue master"]
Drinks = ["water", "coffee", "tea", "milk", "root beer"]

# Indices for quick reference
idx_name = {n: i for i, n in enumerate(Names)}
idx_bday = {b: i for i, b in enumerate(Birthdays)}
idx_cigar = {c: i for i, c in enumerate(Cigars)}
idx_drink = {d: i for i, d in enumerate(Drinks)}

# Variables: for each house (1..5), assign an index for each attribute
N = 5
name = [Int(f"name_{i+1}") for i in range(N)]
bday = [Int(f"bday_{i+1}") for i in range(N)]
cigar = [Int(f"cigar_{i+1}") for i in range(N)]
drink = [Int(f"drink_{i+1}") for i in range(N)]

s = Solver()

# Domains: 0..4 for all attributes
for i in range(N):
    s.add(And(name[i] >= 0, name[i] <= 4))
    s.add(And(bday[i] >= 0, bday[i] <= 4))
    s.add(And(cigar[i] >= 0, cigar[i] <= 4))
    s.add(And(drink[i] >= 0, drink[i] <= 4))

# AllDifferent constraints per attribute category
s.add(Distinct(name))
s.add(Distinct(bday))
s.add(Distinct(cigar))
s.add(Distinct(drink))

# Clues encoding

# 1. The root beer lover is Eric.
for i in range(N):
    s.add(Implies(drink[i] == idx_drink["root beer"], name[i] == idx_name["Eric"]))
    s.add(Implies(name[i] == idx_name["Eric"], drink[i] == idx_drink["root beer"]))

# 2. The person partial to Pall Mall is in the third house.
s.add(cigar[2] == idx_cigar["pall mall"])

# 3. The person whose birthday is in April is Bob.
for i in range(N):
    s.add(Implies(bday[i] == idx_bday["april"], name[i] == idx_name["Bob"]))
    s.add(Implies(name[i] == idx_name["Bob"], bday[i] == idx_bday["april"]))

# 4. The Dunhill smoker is the person whose birthday is in March.
for i in range(N):
    s.add(Implies(cigar[i] == idx_cigar["dunhill"], bday[i] == idx_bday["mar"]))
    s.add(Implies(bday[i] == idx_bday["mar"], cigar[i] == idx_cigar["dunhill"]))

# 5. Peter is somewhere to the right of the root beer lover.
for i in range(N):
    s.add(Implies(
        drink[i] == idx_drink["root beer"],
        Or([name[j] == idx_name["Peter"] for j in range(i+1, N)])
    ))

# 6. There is one house between the person whose birthday is in January and Peter.
for i in range(N):
    conds = []
    if i + 2 < N:
        conds.append(name[i+2] == idx_name["Peter"])
    if i - 2 >= 0:
        conds.append(name[i-2] == idx_name["Peter"])
    s.add(Implies(bday[i] == idx_bday["jan"], Or(conds)))

# 7. The person who smokes many unique blends is the person whose birthday is in February.
for i in range(N):
    s.add(Implies(cigar[i] == idx_cigar["blends"], bday[i] == idx_bday["feb"]))
    s.add(Implies(bday[i] == idx_bday["feb"], cigar[i] == idx_cigar["blends"]))

# 8. The person whose birthday is in February is in the second house.
s.add(bday[1] == idx_bday["feb"])

# 9. Arnold is directly left of Peter.
for i in range(N):
    if i + 1 < N:
        s.add(Implies(name[i] == idx_name["Arnold"], name[i+1] == idx_name["Peter"]))
    else:
        s.add(name[i] != idx_name["Arnold"])

# 10. The person who likes milk is not in the fifth house.
s.add(drink[4] != idx_drink["milk"])

# 11. The person who smokes Blue Master is the coffee drinker.
for i in range(N):
    s.add(Implies(cigar[i] == idx_cigar["blue master"], drink[i] == idx_drink["coffee"]))
    s.add(Implies(drink[i] == idx_drink["coffee"], cigar[i] == idx_cigar["blue master"]))

# 12. There is one house between the tea drinker and the coffee drinker.
for i in range(N):
    conds = []
    if i + 2 < N:
        conds.append(drink[i+2] == idx_drink["tea"])
    if i - 2 >= 0:
        conds.append(drink[i-2] == idx_drink["tea"])
    s.add(Implies(drink[i] == idx_drink["coffee"], Or(conds)))

# 13. Eric is in the third house.
s.add(name[2] == idx_name["Eric"])

# Solve
if s.check() != sat:
    raise RuntimeError("No solution found")

m = s.model()

# Build the JSON output
rows = []
for i in range(N):
    house_num = str(i + 1)
    n = Names[m[name[i]].as_long()]
    b = Birthdays[m[bday[i]].as_long()]
    c = Cigars[m[cigar[i]].as_long()]
    d = Drinks[m[drink[i]].as_long()]
    rows.append([house_num, n, b, c, d])

output = {
    "solution": {
        "header": ["House", "Name", "Birthday", "Cigar", "Drink"],
        "rows": rows
    }
}

print(json.dumps(output, ensure_ascii=False, indent=2))