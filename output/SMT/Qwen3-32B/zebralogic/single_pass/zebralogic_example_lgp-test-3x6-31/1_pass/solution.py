import z3
import json

s = z3.Solver()

houses = 3

# Create variables for each attribute per house
name = [z3.Int(f'name_{i}') for i in range(houses)]
drink = [z3.Int(f'drink_{i}') for i in range(houses)]
vacation = [z3.Int(f'vacation_{i}') for i in range(houses)]
houseStyle = [z3.Int(f'houseStyle_{i}') for i in range(houses)]
animal = [z3.Int(f'animal_{i}') for i in range(houses)]
birthday = [z3.Int(f'birthday_{i}') for i in range(houses)]

# Add constraints for each attribute to be unique (distinct)
for var in [name, drink, vacation, houseStyle, animal, birthday]:
    s.add(z3.Distinct(var))

# Add bounds (0-2)
for i in range(houses):
    for var in [name[i], drink[i], vacation[i], houseStyle[i], animal[i], birthday[i]]:
        s.add(z3.And(var >= 0, var <= 2))

# Now add per-clue constraints

# Clue 1: colonial (houseStyle[i] == 0) is left of milk (drink[j] == 0)
for i in range(houses):
    for j in range(houses):
        s.add(z3.Implies(z3.And(houseStyle[i] == 0, drink[j] == 0), i < j))

# Clue 2: city (vacation[i] == 1) directly left of victorian (houseStyle[i+1] == 1)
s.add(z3.Or(
    z3.And(vacation[0] == 1, houseStyle[1] == 1),
    z3.And(vacation[1] == 1, houseStyle[2] == 1)
))

# Clue 3: jan (birthday[i] == 0) directly left of cat (animal[j] == 0)
s.add(z3.Or(
    z3.And(birthday[0] == 0, animal[1] == 0),
    z3.And(birthday[1] == 0, animal[2] == 0)
))

# Clue 4: water (drink[i] == 1) is mountain (vacation[i] == 0)
for i in range(houses):
    s.add(z3.Implies(drink[i] == 1, vacation[i] == 0))
    s.add(z3.Implies(vacation[i] == 0, drink[i] == 1))

# Clue 5: animal[i] == 2 (horse) → name[i] == 1 (Peter)
for i in range(houses):
    s.add(z3.Implies(animal[i] == 2, name[i] == 1))
    s.add(z3.Implies(name[i] == 1, animal[i] == 2))

# Clue 6: victorian (houseStyle[j] == 1) is to the right of beach (vacation[i] == 2)
for i in range(houses):
    for j in range(houses):
        s.add(z3.Implies(z3.And(vacation[i] == 2, houseStyle[j] == 1), i < j))

# Clue 7: Peter (name[i] == 1) has city (vacation[i] == 1)
for i in range(houses):
    s.add(z3.Implies(name[i] == 1, vacation[i] == 1))
    s.add(z3.Implies(vacation[i] == 1, name[i] == 1))

# Clue 8: mountain (vacation[i] == 0) → birthday[i] == 2 (april)
for i in range(houses):
    s.add(z3.Implies(vacation[i] == 0, birthday[i] == 2))
    s.add(z3.Implies(birthday[i] == 2, vacation[i] == 0))

# Clue 9: Eric (name[i] == 0) → drink[i] == 1 (water)
for i in range(houses):
    s.add(z3.Implies(name[i] == 0, drink[i] == 1))
    s.add(z3.Implies(drink[i] == 1, name[i] == 0))

# Check if the constraints are satisfiable
if s.check() == z3.sat:
    model = s.model()
    # Now extract the values for each house
    solution = []
    for i in range(houses):
        house_num = i + 1
        n = model[name[i]].as_long()
        d = model[drink[i]].as_long()
        v = model[vacation[i]].as_long()
        hs = model[houseStyle[i]].as_long()
        a = model[animal[i]].as_long()
        b = model[birthday[i]].as_long()
        # Map to strings
        name_str = ["Eric", "Peter", "Arnold"][n]
        drink_str = ["milk", "water", "tea"][d]
        vacation_str = ["mountain", "city", "beach"][v]
        houseStyle_str = ["colonial", "victorian", "ranch"][hs]
        animal_str = ["cat", "bird", "horse"][a]
        birthday_str = ["jan", "sept", "april"][b]
        solution.append([str(house_num), name_str, drink_str, vacation_str, houseStyle_str, animal_str, birthday_str])
    # Now format as JSON
    output = {
        "solution": {
            "header": ["House", "Name", "Drink", "Vacation", "HouseStyle", "Animal", "Birthday"],
            "rows": solution
        }
    }
    print(json.dumps(output, indent=2))
else:
    print("No solution found")