from z3 import *

# Create a solver instance
s = Solver()

# Define the houses
houses = [1, 2, 3, 4, 5]

# Define the attributes
names = ["Bob", "Arnold", "Peter", "Alice", "Eric"]
drinks = ["milk", "root beer", "coffee", "tea", "water"]
colors = ["blue", "green", "white", "yellow", "red"]
flowers = ["daffodils", "roses", "lilies", "tulips", "carnations"]
hobbies = ["painting", "cooking", "photography", "gardening", "knitting"]

# Create dictionaries to hold the variables for each attribute per house
name = {h: String(f"name_{h}") for h in houses}
drink = {h: String(f"drink_{h}") for h in houses}
color = {h: String(f"color_{h}") for h in houses}
flower = {h: String(f"flower_{h}") for h in houses}
hobby = {h: String(f"hobby_{h}") for h in houses}

# Add constraints that each attribute in each house is one of the possible values
for h in houses:
    s.add(Or([name[h] == n for n in names]))
    s.add(Or([drink[h] == d for d in drinks]))
    s.add(Or([color[h] == c for c in colors]))
    s.add(Or([flower[h] == f for f in flowers]))
    s.add(Or([hobby[h] == o for o in hobbies]))

# Add constraints that all attributes in each category are distinct
s.add(Distinct([name[h] for h in houses]))
s.add(Distinct([drink[h] for h in houses]))
s.add(Distinct([color[h] for h in houses]))
s.add(Distinct([flower[h] for h in houses]))
s.add(Distinct([hobby[h] for h in houses]))

# Clue 1: Alice is not in the fourth house.
s.add(name[4] != "Alice")

# Clue 2: The root beer lover is the person who enjoys gardening.
for h in houses:
    s.add(Implies(drink[h] == "root beer", hobby[h] == "gardening"))

# Clue 3: The person whose favorite color is green is the coffee drinker.
for h in houses:
    s.add(Implies(color[h] == "green", drink[h] == "coffee"))

# Clue 4: The person whose favorite color is green is the person who loves the bouquet of lilies.
for h in houses:
    s.add(Implies(color[h] == "green", flower[h] == "lilies"))

# Clue 5: The person who loves blue is somewhere to the right of the person who loves a bouquet of daffodils.
for h1 in houses:
    for h2 in houses:
        if h1 < h2:
            s.add(Implies(flower[h1] == "daffodils", color[h2] == "blue"))

# Clue 6: The person who loves cooking is the person who loves blue.
for h in houses:
    s.add(Implies(hobby[h] == "cooking", color[h] == "blue"))

# Clue 7: Eric is directly left of the tea drinker.
for h in range(1, 5):
    s.add(Implies(name[h] == "Eric", drink[h+1] == "tea"))

# Clue 8: The one who only drinks water is Peter.
for h in houses:
    s.add(Implies(drink[h] == "water", name[h] == "Peter"))

# Clue 9: Arnold is the photography enthusiast.
for h in houses:
    s.add(Implies(name[h] == "Arnold", hobby[h] == "photography"))

# Clue 10: The person who loves white is the person who loves the rose bouquet.
for h in houses:
    s.add(Implies(color[h] == "white", flower[h] == "roses"))

# Clue 11: There is one house between the person who loves a carnations arrangement and the person whose favorite color is red.
for h1 in houses:
    for h2 in houses:
        if h1 + 2 == h2:
            s.add(Implies(flower[h1] == "carnations", color[h2] == "red"))

# Clue 12: The person who loves cooking is somewhere to the left of the person who paints as a hobby.
for h1 in houses:
    for h2 in houses:
        if h1 < h2:
            s.add(Implies(hobby[h1] == "cooking", hobby[h2] == "painting"))

# Clue 13: The one who only drinks water is in the third house.
s.add(drink[3] == "water")

# Clue 14: The person who loves a carnations arrangement is the root beer lover.
for h in houses:
    s.add(Implies(flower[h] == "carnations", drink[h] == "root beer"))

# Clue 15: The person who loves white is in the second house.
s.add(color[2] == "white")

# Check if the problem is satisfiable
if s.check() == sat:
    model = s.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Drink", "Color", "Flower", "Hobby"],
            "rows": []
        }
    }
    for h in houses:
        row = [
            str(h),
            model.eval(name[h]).as_string(),
            model.eval(drink[h]).as_string(),
            model.eval(color[h]).as_string(),
            model.eval(flower[h]).as_string(),
            model.eval(hobby[h]).as_string()
        ]
        solution["solution"]["rows"].append(row)
    print(solution)
else:
    print("No solution found")