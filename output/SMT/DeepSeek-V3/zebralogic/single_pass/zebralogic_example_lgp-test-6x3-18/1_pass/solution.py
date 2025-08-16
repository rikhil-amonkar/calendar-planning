import json
from z3 import *

# Initialize the solver
s = Solver()

# Define the houses
houses = [1, 2, 3, 4, 5, 6]

# Define the attributes
names = ["Arnold", "Eric", "Bob", "Alice", "Carol", "Peter"]
mothers = ["Sarah", "Holly", "Janelle", "Aniya", "Penny", "Kailyn"]
pets = ["hamster", "dog", "bird", "cat", "fish", "rabbit"]

# Create variables for each attribute in each house
name = {h: String(f"name_{h}") for h in houses}
mother = {h: String(f"mother_{h}") for h in houses}
pet = {h: String(f"pet_{h}") for h in houses}

# Add constraints that all attributes are unique in each category
s.add(Distinct([name[h] for h in houses]))
s.add(Distinct([mother[h] for h in houses]))
s.add(Distinct([pet[h] for h in houses]))

# Each attribute must be one of the given options
for h in houses:
    s.add(Or([name[h] == n for n in names]))
    s.add(Or([mother[h] == m for m in mothers]))
    s.add(Or([pet[h] == p for p in pets]))

# Add the clues as constraints
# Clue 1: Bob is not in the second house.
s.add(name[2] != "Bob")

# Clue 2: There are two houses between the person who has a cat and the person who owns a rabbit.
# This means if cat is in house X, rabbit is in house X+3, or vice versa is not possible because there are only 6 houses.
for h in houses:
    if h + 3 <= 6:
        s.add(Implies(pet[h] == "cat", pet[h + 3] == "rabbit"))
    else:
        s.add(pet[h] != "cat")  # cat cannot be in houses 4,5,6 because rabbit would be beyond house 6

# Clue 3: The person who has a cat is directly left of the person whose mother's name is Holly.
# This means cat is in house X, mother in X+1 is Holly.
for h in houses:
    if h + 1 <= 6:
        s.add(Implies(pet[h] == "cat", mother[h + 1] == "Holly"))
    else:
        s.add(pet[h] != "cat")  # cat cannot be in house 6

# Clue 4: The person with a pet hamster is directly left of the person who owns a rabbit.
# hamster in X, rabbit in X+1.
for h in houses:
    if h + 1 <= 6:
        s.add(Implies(pet[h] == "hamster", pet[h + 1] == "rabbit"))
    else:
        s.add(pet[h] != "hamster")  # hamster cannot be in house 6

# Clue 5: The person who owns a rabbit is Eric.
for h in houses:
    s.add(Implies(pet[h] == "rabbit", name[h] == "Eric"))

# Clue 6: There is one house between the person who owns a dog and the person who has a cat.
# dog in X, cat in X+2, or cat in X, dog in X-2.
for h in houses:
    if h + 2 <= 6:
        s.add(Implies(pet[h] == "dog", pet[h + 2] == "cat"))
    if h - 2 >= 1:
        s.add(Implies(pet[h] == "cat", pet[h - 2] == "dog"))

# Clue 7: The person who has a cat is the person whose mother's name is Janelle.
for h in houses:
    s.add(Implies(pet[h] == "cat", mother[h] == "Janelle"))

# Clue 8: Alice is directly left of Carol.
# Alice in X, Carol in X+1.
for h in houses:
    if h + 1 <= 6:
        s.add(Implies(name[h] == "Alice", name[h + 1] == "Carol"))
    else:
        s.add(name[h] != "Alice")  # Alice cannot be in house 6

# Clue 9: Carol is the person whose mother's name is Aniya.
for h in houses:
    s.add(Implies(name[h] == "Carol", mother[h] == "Aniya"))

# Clue 10: Arnold is the person who has a cat.
for h in houses:
    s.add(Implies(name[h] == "Arnold", pet[h] == "cat"))

# Clue 11: The person whose mother's name is Kailyn is the person who owns a rabbit.
for h in houses:
    s.add(Implies(mother[h] == "Kailyn", pet[h] == "rabbit"))

# Clue 12: The person with an aquarium of fish is the person whose mother's name is Sarah.
for h in houses:
    s.add(Implies(pet[h] == "fish", mother[h] == "Sarah"))

# Solve the problem
if s.check() == sat:
    model = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Mother", "Pet"],
            "rows": []
        }
    }
    for h in houses:
        row = [
            str(h),
            model.eval(name[h]).as_string(),
            model.eval(mother[h]).as_string(),
            model.eval(pet[h]).as_string()
        ]
        solution["solution"]["rows"].append(row)
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")