from z3 import *
import json

# Define our mappings for names and hair colors.
names_map = {"Alice": 0, "Arnold": 1, "Peter": 2, "Eric": 3}
names_list = ["Alice", "Arnold", "Peter", "Eric"]

hair_map = {"black": 0, "blonde": 1, "brown": 2, "red": 3}
hair_list = ["black", "blonde", "brown", "red"]

# There are 4 houses (indexed 0 to 3 corresponding to houses 1 to 4)
houses = 4

# Create Z3 solver instance
s = Solver()

# Create integer variables for each house's name and hair color
name_vars = [Int(f"name_{i}") for i in range(houses)]
hair_vars = [Int(f"hair_{i}") for i in range(houses)]

# Each variable must be one of the 4 possible options (0,1,2,3)
for i in range(houses):
    s.add(And(name_vars[i] >= 0, name_vars[i] < 4))
    s.add(And(hair_vars[i] >= 0, hair_vars[i] < 4))

# All houses have distinct names and distinct hair colors.
s.add(Distinct(name_vars))
s.add(Distinct(hair_vars))

# Clue 5: Alice is in the first house.
s.add(name_vars[0] == names_map["Alice"])

# Clue 2: Alice and Arnold are next to each other.
# Since Alice is in the first house (house index 0), the only adjacent house is index 1.
s.add(name_vars[1] == names_map["Arnold"])

# Clue 1: Eric is directly left of the person who has blonde hair.
# This means for some house i (0,1,2), if house i has Eric then house i+1 must have blonde hair.
s.add(Or(And(name_vars[0] == names_map["Eric"], hair_vars[1] == hair_map["blonde"]),
         And(name_vars[1] == names_map["Eric"], hair_vars[2] == hair_map["blonde"]),
         And(name_vars[2] == names_map["Eric"], hair_vars[3] == hair_map["blonde"])))

# Clue 3: Eric has brown hair.
# For each house if the person is Eric then the hair color must be brown.
for i in range(houses):
    s.add(Implies(name_vars[i] == names_map["Eric"], hair_vars[i] == hair_map["brown"]))

# Clue 4: The person who has black hair is not in the first house.
s.add(hair_vars[0] != hair_map["black"])

# Solve the constraints.
if s.check() == sat:
    m = s.model()
    rows = []
    # Houses are numbered 1 to 4 (left to right)
    for i in range(houses):
        house_number = str(i+1)
        person = names_list[m.evaluate(name_vars[i]).as_long()]
        hair = hair_list[m.evaluate(hair_vars[i]).as_long()]
        rows.append([house_number, person, hair])
    
    solution_data = {
        "solution": {
            "header": ["House", "Name", "HairColor"],
            "rows": rows
        }
    }
    
    print(json.dumps(solution_data, indent=2))
else:
    print("No solution found")