from z3 import *
import json

# Create a solver instance
solver = Solver()

houses_count = 5

# For each house (indexed 0..4 corresponding to Houses 1..5) we define an integer variable for each attribute.
names   = [Int(f"name_{i}")   for i in range(houses_count)]
styles  = [Int(f"style_{i}")  for i in range(houses_count)]
mothers = [Int(f"mother_{i}") for i in range(houses_count)]
phones  = [Int(f"phone_{i}")  for i in range(houses_count)]
drinks  = [Int(f"drink_{i}")  for i in range(houses_count)]
animals = [Int(f"animal_{i}") for i in range(houses_count)]

# Domain for each variable is 0..4 (five possibilities)
for lst in [names, styles, mothers, phones, drinks, animals]:
    for var in lst:
        solver.add(var >= 0, var < houses_count)

# All attributes must be all-different.
solver.add(Distinct(names))
solver.add(Distinct(styles))
solver.add(Distinct(mothers))
solver.add(Distinct(phones))
solver.add(Distinct(drinks))
solver.add(Distinct(animals))

# We define the following mappings:
# Names:    Peter=0, Arnold=1, Eric=2, Bob=3, Alice=4
# Style:    modern=0, craftsman=1, ranch=2, victorian=3, colonial=4
# Mother:   Penny=0, Kailyn=1, Holly=2, Janelle=3, Aniya=4
# Phone:    oneplus 9=0, google pixel 6=1, huawei p50=2, iphone 13=3, samsung galaxy s21=4
# Drink:    coffee=0, water=1, root beer=2, tea=3, milk=4
# Animal:   fish=0, dog=1, horse=2, bird=3, cat=4

# Clue 1: The person who uses a Google Pixel 6 (phone==1) is not in the first house (index 0).
solver.add(phones[0] != 1)

# Clue 2: The one who only drinks water (drink==1) is Alice (name==4).
for i in range(houses_count):
    solver.add(Implies(names[i] == 4, drinks[i] == 1))
    solver.add(Implies(drinks[i] == 1, names[i] == 4))

# Clue 3: The person living in a colonial-style house (style==4)
# is somewhere to the right of the person who uses a Huawei P50 (phone==2).
for i in range(houses_count):
    for j in range(houses_count):
        solver.add(Implies(And(styles[i] == 4, phones[j] == 2), j < i))

# Clue 4: The person who keeps horses (animal==2) is the person who uses a OnePlus 9 (phone==0).
for i in range(houses_count):
    solver.add(Implies(animals[i] == 2, phones[i] == 0))
    solver.add(Implies(phones[i] == 0, animals[i] == 2))

# Clue 5: The person in a ranch-style home (style==2) is the person whose mother's name is Kailyn (mother==1).
for i in range(houses_count):
    solver.add(Implies(styles[i] == 2, mothers[i] == 1))
    solver.add(Implies(mothers[i] == 1, styles[i] == 2))

# Clue 6: The root beer lover (drink==2) is the cat lover (animal==4).
for i in range(houses_count):
    solver.add(Implies(drinks[i] == 2, animals[i] == 4))
    solver.add(Implies(animals[i] == 4, drinks[i] == 2))

# Clue 7: The person living in a colonial-style house (style==4) is not in the fourth house (index 3).
solver.add(styles[3] != 4)

# Clue 8: The bird keeper (animal==3) is in the fourth house (index 3).
solver.add(animals[3] == 3)

# Clue 9: The tea drinker (drink==3) is Bob (name==3).
for i in range(houses_count):
    solver.add(Implies(drinks[i] == 3, names[i] == 3))
    solver.add(Implies(names[i] == 3, drinks[i] == 3))

# Clue 10: The tea drinker (drink==3) is somewhere to the right of the person whose mother's name is Kailyn (mother==1).
for i in range(houses_count):
    for j in range(houses_count):
        solver.add(Implies(And(drinks[i] == 3, mothers[j] == 1), j < i))

# Clue 11: The root beer lover (drink==2) is somewhere to the left of the person whose mother's name is Kailyn (mother==1).
for i in range(houses_count):
    for j in range(houses_count):
        solver.add(Implies(And(drinks[i] == 2, mothers[j] == 1), i < j))

# Clue 12: The person who keeps horses (animal==2) is in a modern-style house (style==0).
for i in range(houses_count):
    solver.add(Implies(animals[i] == 2, styles[i] == 0))
    solver.add(Implies(styles[i] == 0, animals[i] == 2))

# Clue 13: The person who uses an iPhone 13 (phone==3) is the person who likes milk (drink==4).
for i in range(houses_count):
    solver.add(Implies(phones[i] == 3, drinks[i] == 4))
    solver.add(Implies(drinks[i] == 4, phones[i] == 3))

# Clue 14: The dog owner (animal==1) is the person who likes milk (drink==4).
for i in range(houses_count):
    solver.add(Implies(animals[i] == 1, drinks[i] == 4))
    solver.add(Implies(drinks[i] == 4, animals[i] == 1))

# Clue 15: The person who uses a Google Pixel 6 (phone==1) is in a Craftsman-style house (style==1).
for i in range(houses_count):
    solver.add(Implies(phones[i] == 1, styles[i] == 1))
    solver.add(Implies(styles[i] == 1, phones[i] == 1))

# Clue 16: Eric (name==2) is not in the second house (index 1).
solver.add(names[1] != 2)

# Clue 17: The tea drinker is in the fourth house (index 3).
solver.add(drinks[3] == 3)

# Clue 18: The person who keeps horses is in the third house (index 2).
solver.add(animals[2] == 2)

# Clue 19: The person in a modern-style house (style==0) is the person whose mother's name is Penny (mother==0).
for i in range(houses_count):
    solver.add(Implies(styles[i] == 0, mothers[i] == 0))
    solver.add(Implies(mothers[i] == 0, styles[i] == 0))

# Clue 20: The root beer lover (drink==2) is Peter (name==0).
for i in range(houses_count):
    solver.add(Implies(drinks[i] == 2, names[i] == 0))
    solver.add(Implies(names[i] == 0, drinks[i] == 2))

# Clue 21: The person whose mother's name is Aniya (mother==4) is not in the fourth house (index 3).
solver.add(mothers[3] != 4)

# Clue 22: The person whose mother's name is Janelle (mother==3) drinks water (drink==1).
for i in range(houses_count):
    solver.add(Implies(mothers[i] == 3, drinks[i] == 1))
    solver.add(Implies(drinks[i] == 1, mothers[i] == 3))

# Check satisfiability and extract the solution.
if solver.check() == sat:
    m = solver.model()

    # Reverse mapping dictionaries to convert numeric values to strings.
    names_map   = {0: "Peter", 1: "Arnold", 2: "Eric", 3: "Bob", 4: "Alice"}
    styles_map  = {0: "modern", 1: "craftsman", 2: "ranch", 3: "victorian", 4: "colonial"}
    mothers_map = {0: "Penny", 1: "Kailyn", 2: "Holly", 3: "Janelle", 4: "Aniya"}
    phones_map  = {0: "oneplus 9", 1: "google pixel 6", 2: "huawei p50", 3: "iphone 13", 4: "samsung galaxy s21"}
    drinks_map  = {0: "coffee", 1: "water", 2: "root beer", 3: "tea", 4: "milk"}
    animals_map = {0: "fish", 1: "dog", 2: "horse", 3: "bird", 4: "cat"}

    # Build solution output keeping the houses in order.
    solution = {
        "header": ["House", "Name", "HouseStyle", "Mother", "PhoneModel", "Drink", "Animal"],
        "rows": []
    }

    for i in range(houses_count):
        house_number = str(i + 1)
        row = [
            house_number,
            names_map[m.evaluate(names[i]).as_long()],
            styles_map[m.evaluate(styles[i]).as_long()],
            mothers_map[m.evaluate(mothers[i]).as_long()],
            phones_map[m.evaluate(phones[i]).as_long()],
            drinks_map[m.evaluate(drinks[i]).as_long()],
            animals_map[m.evaluate(animals[i]).as_long()]
        ]
        solution["rows"].append(row)

    # Create final JSON dictionary with the required structure.
    output = {"solution": solution}
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")