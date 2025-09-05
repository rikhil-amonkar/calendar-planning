from z3 import *
import json

# Define the domains (we use integers to represent each distinct attribute)
# Names: Bob=0, Arnold=1, Alice=2, Peter=3, Eric=4
# Hobbies: cooking=0, gardening=1, painting=2, photography=3, knitting=4
# FavoriteSports: swimming=0, tennis=1, soccer=2, baseball=3, basketball=4
# HouseStyles: ranch=0, craftsman=1, victorian=2, modern=3, colonial=4
# Children: Timothy=0, Samantha=1, Bella=2, Meredith=3, Fred=4
# Heights: average=0, very tall=1, very short=2, short=3, tall=4

names_list = ["Bob", "Arnold", "Alice", "Peter", "Eric"]
hobbies_list = ["cooking", "gardening", "painting", "photography", "knitting"]
sports_list = ["swimming", "tennis", "soccer", "baseball", "basketball"]
styles_list = ["ranch", "craftsman", "victorian", "modern", "colonial"]
children_list = ["Timothy", "Samantha", "Bella", "Meredith", "Fred"]
heights_list = ["average", "very tall", "very short", "short", "tall"]

solver = Solver()

# Create 5 houses (index 0 to 4 represent houses 1 to 5)
houses_count = 5

# Each house gets an assignment for each attribute, represented as an Int variable.
names = [Int(f"name_{i}") for i in range(houses_count)]
hobbies = [Int(f"hobby_{i}") for i in range(houses_count)]
sports = [Int(f"sport_{i}") for i in range(houses_count)]
styles = [Int(f"style_{i}") for i in range(houses_count)]
children = [Int(f"child_{i}") for i in range(houses_count)]
heights = [Int(f"height_{i}") for i in range(houses_count)]

# Domain constraints: each variable is in 0..4
for i in range(houses_count):
    solver.add(And(names[i] >= 0, names[i] < 5))
    solver.add(And(hobbies[i] >= 0, hobbies[i] < 5))
    solver.add(And(sports[i] >= 0, sports[i] < 5))
    solver.add(And(styles[i] >= 0, styles[i] < 5))
    solver.add(And(children[i] >= 0, children[i] < 5))
    solver.add(And(heights[i] >= 0, heights[i] < 5))

# All attributes are unique across houses:
solver.add(Distinct(names))
solver.add(Distinct(hobbies))
solver.add(Distinct(sports))
solver.add(Distinct(styles))
solver.add(Distinct(children))
solver.add(Distinct(heights))

# Clue 1: The person who has an average height (0) has child named Meredith (3).
for i in range(houses_count):
    solver.add(Implies(heights[i] == 0, children[i] == 3))
    solver.add(Implies(children[i] == 3, heights[i] == 0))

# Clue 2: The person who is tall (4) is in the second house (index 1).
solver.add(heights[1] == 4)

# Clue 20: The person residing in a Victorian house (2) is in the fifth house (index 4).
solver.add(styles[4] == 2)

# Clue 3: Peter is directly left of the person residing in a Victorian house.
# With Clue 20, Victorian is in house 5 (index 4), so Peter must be in house 4 (index 3).
solver.add(names[3] == 3)  # Peter's index is 3

# Clue 4: Alice is the person who is tall.
# Since tall is 4 and already house index 1 has height 4, Alice must be in house 2 (index 1).
solver.add(names[1] == 2)  # Alice's index is 2

# Clue 5: The person who loves baseball (3) is the person who is very tall (1).
for i in range(houses_count):
    solver.add(Implies(sports[i] == 3, heights[i] == 1))
    solver.add(Implies(heights[i] == 1, sports[i] == 3))

# Clue 6: The house whose child is named Meredith (3) is next to the house whose child is Timothy (0).
for i in range(houses_count):
    for j in range(houses_count):
        solver.add(Implies(And(children[i] == 3, children[j] == 0), Abs(i - j) == 1))

# Clue 7: Bob (0) is the person who paints as a hobby (painting=2).
for i in range(houses_count):
    solver.add(Implies(names[i] == 0, hobbies[i] == 2))
    solver.add(Implies(hobbies[i] == 2, names[i] == 0))

# Clue 8: The person who enjoys gardening (1) is in the second house (index 1).
solver.add(hobbies[1] == 1)

# Clue 9: The person who is very short (2) is somewhere to the right of Eric (4).
for i in range(houses_count):
    for j in range(houses_count):
        solver.add(Implies(And(names[i] == 4, heights[j] == 2), j > i))

# Clue 10: The person who loves tennis (1) is the person whose child is named Samantha (1).
for i in range(houses_count):
    solver.add(Implies(sports[i] == 1, children[i] == 1))
    solver.add(Implies(children[i] == 1, sports[i] == 1))

# Clue 11: The person who loves soccer (2) is not in the first house (index 0).
solver.add(sports[0] != 2)

# Clue 12: The person whose child is named Samantha (1) is in a modern-style house (3).
for i in range(houses_count):
    solver.add(Implies(children[i] == 1, styles[i] == 3))
    solver.add(Implies(styles[i] == 3, children[i] == 1))

# Clue 13: The person in a Craftsman-style house (1) is the person who has an average height (0).
for i in range(houses_count):
    solver.add(Implies(styles[i] == 1, heights[i] == 0))
    solver.add(Implies(heights[i] == 0, styles[i] == 1))

# Clue 14: The person whose child is named Fred (4) is the person residing in a Victorian house (2).
for i in range(houses_count):
    solver.add(Implies(children[i] == 4, styles[i] == 2))
    solver.add(Implies(styles[i] == 2, children[i] == 4))

# Clue 15: The person who is short (3) is the person who loves basketball (4).
for i in range(houses_count):
    solver.add(Implies(heights[i] == 3, sports[i] == 4))
    solver.add(Implies(sports[i] == 4, heights[i] == 3))

# Clue 16: Peter is the person who is very tall (1).
for i in range(houses_count):
    solver.add(Implies(names[i] == 3, heights[i] == 1))

# Clue 17: The person in a ranch-style home (0) is somewhere to the left of the person who loves cooking (0).
for i in range(houses_count):
    for j in range(houses_count):
        solver.add(Implies(And(styles[i] == 0, hobbies[j] == 0), i < j))

# Clue 18: The person who enjoys knitting (4) and the person who enjoys gardening (1) are next to each other.
for i in range(houses_count):
    for j in range(houses_count):
        solver.add(Implies(And(hobbies[i] == 4, hobbies[j] == 1), Abs(i - j) == 1))

# Clue 19: The person in a modern-style house (3) is the person who loves cooking (0).
for i in range(houses_count):
    solver.add(Implies(styles[i] == 3, hobbies[i] == 0))
    solver.add(Implies(hobbies[i] == 0, styles[i] == 3))

# Solve the puzzle
if solver.check() == sat:
    model = solver.model()
    solution_rows = []
    # Build the result rows in order (house 1, house 2, ..., house 5)
    for i in range(houses_count):
        house_number = str(i + 1)
        name_val = model[names[i]].as_long()
        hobby_val = model[hobbies[i]].as_long()
        sport_val = model[sports[i]].as_long()
        style_val = model[styles[i]].as_long()
        child_val = model[children[i]].as_long()
        height_val = model[heights[i]].as_long()
        row = [
            house_number,
            names_list[name_val],
            hobbies_list[hobby_val],
            sports_list[sport_val],
            styles_list[style_val],
            children_list[child_val],
            heights_list[height_val]
        ]
        solution_rows.append(row)
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Hobby", "FavoriteSport", "HouseStyle", "Children", "Height"],
            "rows": solution_rows
        }
    }
    print(json.dumps(solution))
else:
    print(json.dumps({"solution": "No solution found"}))