from z3 import Solver, Int, And, Distinct, sat
import json

# Define houses and attributes
houses = [1, 2]

names = ["Eric", "Arnold"]
book_genres = ["science fiction", "mystery"]
birthdays = ["april", "sept"]
animals = ["horse", "cat"]

# Create Z3 variables for each attribute value -> house mapping
v_name = {n: Int(f"Name_{n}") for n in names}
v_book = {b: Int(f"Book_{b.replace(' ', '_')}") for b in book_genres}
v_bday = {d: Int(f"Birthday_{d}") for d in birthdays}
v_animal = {a: Int(f"Animal_{a}") for a in animals}

s = Solver()

# Domain constraints: each variable is a house number
for var in list(v_name.values()) + list(v_book.values()) + list(v_bday.values()) + list(v_animal.values()):
    s.add(And(var >= 1, var <= 2))

# Uniqueness constraints within each attribute category
s.add(Distinct(*v_name.values()))
s.add(Distinct(*v_book.values()))
s.add(Distinct(*v_bday.values()))
s.add(Distinct(*v_animal.values()))

# Clues:
# 1. Eric is in the first house.
s.add(v_name["Eric"] == 1)

# 2. Eric is the person whose birthday is in September.
s.add(v_name["Eric"] == v_bday["sept"])

# 3. The person who loves science fiction books is in the second house.
s.add(v_book["science fiction"] == 2)

# 4. The person who keeps horses is the person whose birthday is in September.
s.add(v_animal["horse"] == v_bday["sept"])

if s.check() != sat:
    raise RuntimeError("No solution found")

m = s.model()

# Helper to invert mapping from attribute value -> house to house -> attribute value
def value_for_house(var_map, house):
    for val, var in var_map.items():
        if m[var].as_long() == house:
            return val
    return None

# Build the JSON result
header = ["House", "Name", "BookGenre", "Birthday", "Animal"]
rows = []
for h in houses:
    rows.append([
        str(h),
        value_for_house(v_name, h),
        value_for_house(v_book, h),
        value_for_house(v_bday, h),
        value_for_house(v_animal, h),
    ])

result = {
    "solution": {
        "header": header,
        "rows": rows
    }
}

print(json.dumps(result))