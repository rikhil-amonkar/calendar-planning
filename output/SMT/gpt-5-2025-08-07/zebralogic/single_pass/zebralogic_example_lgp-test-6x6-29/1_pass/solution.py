# Solve the logic puzzle with Z3 and print the JSON result.
# Requires: z3-solver (pip install z3-solver)

from z3 import *
import json

# Houses are indexed 0..5 (left to right). We'll print as 1..6 at the end.
N = 6
IDX = list(range(N))

# Attribute values
Names = ["Arnold", "Carol", "Peter", "Eric", "Bob", "Alice"]
HouseStyles = ["ranch", "colonial", "modern", "craftsman", "mediterranean", "victorian"]
Foods = ["pizza", "stew", "spaghetti", "grilled cheese", "stir fry", "soup"]
Vacations = ["cultural", "cruise", "mountain", "camping", "city", "beach"]
Heights = ["average", "very tall", "very short", "short", "tall", "super tall"]
Cigars = ["yellow monster", "prince", "dunhill", "pall mall", "blue master", "blends"]

# Create Z3 Int vars mapping each value to a house index 0..5
def mk_pos_vars(vals, prefix):
    return {v: Int(f"{prefix}_{v.replace(' ', '_')}") for v in vals}

pos_name = mk_pos_vars(Names, "name")
pos_style = mk_pos_vars(HouseStyles, "style")
pos_food = mk_pos_vars(Foods, "food")
pos_vac = mk_pos_vars(Vacations, "vac")
pos_height = mk_pos_vars(Heights, "height")
pos_cigar = mk_pos_vars(Cigars, "cigar")

s = Solver()

# Every variable in 0..5
for d in [pos_name, pos_style, pos_food, pos_vac, pos_height, pos_cigar]:
    for v in d.values():
        s.add(v >= 0, v < N)

# AllDifferent within each attribute category
def alldiff(values):
    s.add(Distinct(*values))

alldiff(list(pos_name.values()))
alldiff(list(pos_style.values()))
alldiff(list(pos_food.values()))
alldiff(list(pos_vac.values()))
alldiff(list(pos_height.values()))
alldiff(list(pos_cigar.values()))

# "Loves" relation:
# We model a bijection L: person_index -> loved_person_index
# Such that each person loves exactly one person and each person is loved by exactly one person.
L = [Int(f"L_{i}") for i in IDX]
for i in IDX:
    s.add(L[i] >= 0, L[i] < N)
s.add(Distinct(*L))  # images are all distinct -> permutation (and surjective over 0..5)

# Helper to create variables that denote "the person who loves [Food X]" and "the person who loves [Vacation Y]".
# We'll ensure lover_food[X] is exactly the unique i such that L[i] == pos_food[X].
lover_food = {f: Int(f"lover_food_{f.replace(' ', '_')}") for f in Foods}
lover_vac = {v: Int(f"lover_vac_{v.replace(' ', '_')}") for v in Vacations}
for f in Foods:
    s.add(lover_food[f] >= 0, lover_food[f] < N)
    # Equate lover_food[f] with the unique index i such that L[i] == pos_food[f]
    # Encode bi-implication via cases
    disj = []
    for i in IDX:
        # If lover_food[f] == i then L[i] == pos_food[f]
        s.add(Implies(lover_food[f] == i, L[i] == pos_food[f]))
        # If L[i] == pos_food[f] then lover_food[f] == i
        disj.append(L[i] == pos_food[f])
        s.add(Implies(L[i] == pos_food[f], lover_food[f] == i))
    # At least one i satisfies L[i] == pos_food[f] (guaranteed by permutation property), so no extra disjunction needed.

for v in Vacations:
    s.add(lover_vac[v] >= 0, lover_vac[v] < N)
    for i in IDX:
        s.add(Implies(lover_vac[v] == i, L[i] == pos_vac[v]))
        s.add(Implies(L[i] == pos_vac[v], lover_vac[v] == i))

# Convenience helpers
def exactly_k_apart(a, b, k):
    s.add(Or(a - b == k, b - a == k))

def next_to(a, b):
    exactly_k_apart(a, b, 1)

def left_of(a, b):
    s.add(a < b)

def right_of(a, b):
    s.add(a > b)

# Clues encoding:

# 1. Alice is in the fifth house. (index 4)
s.add(pos_name["Alice"] == 4)

# 2. The person who loves stir fry is the person living in a colonial-style house.
s.add(lover_food["stir fry"] == pos_style["colonial"])

# 3. Alice is the person who loves the spaghetti eater.
s.add(lover_food["spaghetti"] == pos_name["Alice"])

# 4. Arnold is the person who loves the stew.
s.add(lover_food["stew"] == pos_name["Arnold"])

# 5. There is one house between the person who has an average height and Peter.
exactly_k_apart(pos_height["average"], pos_name["Peter"], 2)

# 6. The person in a Craftsman-style house is not in the third house. (index 2)
s.add(pos_style["craftsman"] != 2)

# 7. The person who has an average height is the person who loves stir fry.
s.add(pos_height["average"] == lover_food["stir fry"])

# 8. The person who loves beach vacations is the person in a ranch-style home.
s.add(lover_vac["beach"] == pos_style["ranch"])

# 9. Eric is in the fourth house. (index 3)
s.add(pos_name["Eric"] == 3)

# 10. There is one house between the person living in a colonial-style house and the person who enjoys camping trips.
exactly_k_apart(pos_style["colonial"], pos_vac["camping"], 2)

# 11. The person who enjoys mountain retreats is the person who smokes Yellow Monster.
s.add(pos_vac["mountain"] == pos_cigar["yellow monster"])

# 12. The person who enjoys mountain retreats is the person who is very tall.
s.add(pos_vac["mountain"] == pos_height["very tall"])

# 13. The person who enjoys mountain retreats and the Dunhill smoker are next to each other.
next_to(pos_vac["mountain"], pos_cigar["dunhill"])

# 14. The person who loves the spaghetti eater is the person residing in a Victorian house.
s.add(lover_food["spaghetti"] == pos_style["victorian"])

# 15. The person who is tall is the person who loves beach vacations.
s.add(pos_height["tall"] == lover_vac["beach"])

# 16. The person who is tall is somewhere to the left of the person residing in a Victorian house.
left_of(pos_height["tall"], pos_style["victorian"])

# 17. The person who loves stir fry is directly left of Bob.
s.add(lover_food["stir fry"] + 1 == pos_name["Bob"])

# 18. The person in a modern-style house is somewhere to the left of Alice.
left_of(pos_style["modern"], pos_name["Alice"])

# 19. The person in a Craftsman-style house is somewhere to the left of the person who is short.
left_of(pos_style["craftsman"], pos_height["short"])

# 20. The person who loves stir fry is somewhere to the left of the Prince smoker.
left_of(lover_food["stir fry"], pos_cigar["prince"])

# 21. There are two houses between the person who loves eating grilled cheese and the person who is super tall.
exactly_k_apart(lover_food["grilled cheese"], pos_height["super tall"], 3)

# 22. The person in a ranch-style home is the person who smokes Blue Master.
s.add(pos_style["ranch"] == pos_cigar["blue master"])

# 23. The person who smokes many unique blends is directly left of the person who smokes Blue Master.
s.add(pos_cigar["blends"] + 1 == pos_cigar["blue master"])

# 24. The person who goes on cultural tours is the person who is a pizza lover.
s.add(pos_vac["cultural"] == pos_food["pizza"])

# 25. The person who is a pizza lover is somewhere to the left of the person who likes going on cruises.
left_of(pos_food["pizza"], pos_vac["cruise"])

# Solve
if s.check() != sat:
    raise RuntimeError("No solution found")

m = s.model()

# Build inverse maps: for each house index, which value sits there
def invert(pos_map):
    inv = {i: None for i in IDX}
    for k, v in pos_map.items():
        inv[m[v].as_long()] = k
    return inv

inv_name = invert(pos_name)
inv_style = invert(pos_style)
inv_food = invert(pos_food)
inv_vac = invert(pos_vac)
inv_height = invert(pos_height)
inv_cigar = invert(pos_cigar)

rows = []
for i in IDX:
    house_num = str(i + 1)
    row = [
        house_num,
        inv_name[i],
        inv_style[i],
        inv_food[i],
        inv_vac[i],
        inv_height[i],
        inv_cigar[i],
    ]
    rows.append(row)

output = {
    "solution": {
        "header": ["House", "Name", "HouseStyle", "Food", "Vacation", "Height", "Cigar"],
        "rows": rows
    }
}

print(json.dumps(output, ensure_ascii=False, indent=2))