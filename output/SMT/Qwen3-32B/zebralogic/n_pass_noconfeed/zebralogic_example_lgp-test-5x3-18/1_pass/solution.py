from z3 import *
import json

# Initialize the solver
s = Solver()

houses = 5

# Create variables for each house (1-5)
names = [Int(f'name_{i+1}') for i in range(houses)]
flowers = [Int(f'flower_{i+1}') for i in range(houses)]
animals = [Int(f'animal_{i+1}') for i in range(houses)]

# Add constraints for distinctness and valid ranges
for var_list in [names, flowers, animals]:
    for var in var_list:
        s.add(And(var >= 0, var < 5))
    s.add(Distinct(var_list))

# Add constraints based on the clues
# Clue 1: Alice is in the second house
s.add(names[1] == 0)  # names[1] corresponds to house 2

# Clue 5 & 8: Eric keeps horse in house 3
s.add(animals[2] == 1)  # animals[2] corresponds to house 3
s.add(names[2] == 1)    # names[2] corresponds to house 3

# Clue 2: Lilies lover is bird keeper
s.add(Or([And(flowers[i] == 2, animals[i] == 3) for i in range(houses)]))

# Clue 3: Peter is to the right of tulips lover
for h1 in range(houses):
    for h2 in range(houses):
        s.add(Implies(And(flowers[h1] == 0, names[h2] == 4), h2 > h1))

# Clue 4: Fish enthusiast has daffodils
s.add(Or([And(animals[i] == 4, flowers[i] == 3) for i in range(houses)]))

# Clue 6: Two houses between dog owner and Bob
for h_dog in range(houses):
    for h_bob in range(houses):
        s.add(Implies(And(animals[h_dog] == 0, names[h_bob] == 3), Abs(h_dog - h_bob) == 3))

# Clue 7: Fish enthusiast directly left of Bob
for h in range(4):  # Houses 1-4 (indices 0-3)
    s.add(Implies(animals[h] == 4, names[h+1] == 3))
s.add(animals[4] != 4)  # Fish cannot be in house 5

# Clue 9: Carnations directly left of tulips
s.add(Or([And(flowers[h] == 4, flowers[h+1] == 0) for h in range(4)]))

# Clue 10: Cat lover not in first house
s.add(animals[0] != 2)

# Check for solution
if s.check() == sat:
    model = s.model()
    # Map integers to strings
    name_list = ["Alice", "Eric", "Arnold", "Bob", "Peter"]
    flower_list = ["tulips", "roses", "lilies", "daffodils", "carnations"]
    animal_list = ["dog", "horse", "cat", "bird", "fish"]
    
    solution = []
    for i in range(houses):
        house_num = i + 1
        name_val = model[names[i]].as_long()
        flower_val = model[flowers[i]].as_long()
        animal_val = model[animals[i]].as_long()
        solution.append([
            str(house_num),
            name_list[name_val],
            flower_list[flower_val],
            animal_list[animal_val]
        ])
    
    output = {
        "solution": {
            "header": ["House", "Name", "Flower", "Animal"],
            "rows": solution
        }
    }
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")