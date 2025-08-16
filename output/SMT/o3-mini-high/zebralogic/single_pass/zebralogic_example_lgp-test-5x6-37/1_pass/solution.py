from z3 import *
import json

# Define the lists for each attribute and their corresponding index values.
names_list   = ["Bob", "Arnold", "Alice", "Peter", "Eric"]
#  Bob=0, Arnold=1, Alice=2, Peter=3, Eric=4

hobbies_list = ["cooking", "gardening", "painting", "photography", "knitting"]
#  cooking=0, gardening=1, painting=2, photography=3, knitting=4

sports_list  = ["swimming", "tennis", "soccer", "baseball", "basketball"]
#  swimming=0, tennis=1, soccer=2, baseball=3, basketball=4

styles_list  = ["ranch", "craftsman", "victorian", "modern", "colonial"]
#  ranch=0, craftsman=1, victorian=2, modern=3, colonial=4

children_list = ["Timothy", "Samantha", "Bella", "Meredith", "Fred"]
#  Timothy=0, Samantha=1, Bella=2, Meredith=3, Fred=4

heights_list = ["average", "tall", "very tall", "very short", "short"]
#  average=0, tall=1, very tall=2, very short=3, short=4

num_houses = 5

# Create a Z3 solver
solver = Solver()

# Create six arrays of integer variables (one per attribute for each house).
names   = [Int(f"name_{i}")   for i in range(num_houses)]
hobbies = [Int(f"hobby_{i}")  for i in range(num_houses)]
sports  = [Int(f"sport_{i}")  for i in range(num_houses)]
styles  = [Int(f"style_{i}")  for i in range(num_houses)]
children= [Int(f"child_{i}")  for i in range(num_houses)]
heights = [Int(f"height_{i}") for i in range(num_houses)]

# Each variable is in the domain 0..4.
for var in names + hobbies + sports + styles + children + heights:
    solver.add(var >= 0, var < num_houses)

# All values in each category must be distinct.
solver.add(Distinct(names))
solver.add(Distinct(hobbies))
solver.add(Distinct(sports))
solver.add(Distinct(styles))
solver.add(Distinct(children))
solver.add(Distinct(heights))

# Clue 1:
# "The person who has an average height is the person's child is named Meredith."
# (average height = 0, Meredith = 3)
for i in range(num_houses):
    solver.add(Implies(heights[i] == 0, children[i] == 3))

# Clue 2:
# "The person who is tall is in the second house."
# (tall = 1; second house is index 1)
solver.add(heights[1] == 1)

# Clue 3:
# "Peter is directly left of the person residing in a Victorian house."
# (Peter = names index 3; victorian = style index 2)
for i in range(num_houses - 1):
    solver.add(Implies(names[i] == 3, styles[i+1] == 2))
# Peter cannot be in the last house.
solver.add(Not(names[num_houses - 1] == 3))

# Clue 4:
# "Alice is the person who is tall."
# (Alice = names index 2; tall = 1)
# With House2 already tall, force House2 to be Alice.
solver.add(names[1] == 2)

# Clue 5:
# "The person who loves baseball is the person who is very tall."
# (baseball = sport index 3; very tall = height index 2)
for i in range(num_houses):
    solver.add(Implies(sports[i] == 3, heights[i] == 2))
    solver.add(Implies(heights[i] == 2, sports[i] == 3))

# Clue 6:
# "The person's child is named Meredith and the person who is the mother of Timothy are next to each other."
# (Meredith = child index 3, Timothy = child index 0)
for i in range(num_houses):
    for j in range(num_houses):
        solver.add(Implies(And(children[i] == 3, children[j] == 0), Abs(i - j) == 1))

# Clue 7:
# "Bob is the person who paints as a hobby."
# (Bob = names index 0; painting = hobby index 2)
for i in range(num_houses):
    solver.add(Implies(names[i] == 0, hobbies[i] == 2))

# Clue 8:
# "The person who enjoys gardening is in the second house."
# (gardening = hobby index 1; second house = index 1)
solver.add(hobbies[1] == 1)

# Clue 9:
# "The person who is very short is somewhere to the right of Eric."
# (very short = height index 3; Eric = names index 4)
for i in range(num_houses):
    for j in range(num_houses):
        solver.add(Implies(And(heights[i] == 3, names[j] == 4), i > j))

# Clue 10:
# "The person who loves tennis is the person's child is named Samantha."
# (tennis = sport index 1; Samantha = child index 1)
for i in range(num_houses):
    solver.add(Implies(sports[i] == 1, children[i] == 1))
    solver.add(Implies(children[i] == 1, sports[i] == 1))

# Clue 11:
# "The person who loves soccer is not in the first house."
# (soccer = sport index 2; first house = index 0)
solver.add(sports[0] != 2)

# Clue 12:
# "The person's child is named Samantha is the person in a modern-style house."
# (Samantha = child index 1; modern = style index 3)
for i in range(num_houses):
    solver.add(Implies(children[i] == 1, styles[i] == 3))

# Clue 13:
# "The person in a Craftsman-style house is the person who has an average height."
# (Craftsman = style index 1; average = height index 0)
for i in range(num_houses):
    solver.add(Implies(styles[i] == 1, heights[i] == 0))
    solver.add(Implies(heights[i] == 0, styles[i] == 1))

# Clue 14:
# "The person's child is named Fred is the person residing in a Victorian house."
# (Fred = child index 4; victorian = style index 2)
for i in range(num_houses):
    solver.add(Implies(children[i] == 4, styles[i] == 2))

# Clue 15:
# "The person who is short is the person who loves basketball."
# (short = height index 4; basketball = sport index 4)
for i in range(num_houses):
    solver.add(Implies(heights[i] == 4, sports[i] == 4))
    solver.add(Implies(sports[i] == 4, heights[i] == 4))

# Clue 16:
# "Peter is the person who is very tall."
# (Peter = name index 3; very tall = height index 2)
for i in range(num_houses):
    solver.add(Implies(names[i] == 3, heights[i] == 2))

# Clue 17:
# "The person in a ranch-style home is somewhere to the left of the person who loves cooking."
# (ranch-style = style index 0; cooking = hobby index 0)
for i in range(num_houses):
    for j in range(num_houses):
        solver.add(Implies(And(styles[i] == 0, hobbies[j] == 0), i < j))

# Clue 18:
# "The person who enjoys knitting and the person who enjoys gardening are next to each other."
# (knitting = hobby index 4; gardening = hobby index 1)
for i in range(num_houses):
    for j in range(num_houses):
        solver.add(Implies(And(hobbies[i] == 4, hobbies[j] == 1), Abs(i - j) == 1))

# Clue 19:
# "The person in a modern-style house is the person who loves cooking."
# (modern = style index 3; cooking = hobby index 0)
for i in range(num_houses):
    solver.add(Implies(styles[i] == 3, hobbies[i] == 0))
    solver.add(Implies(hobbies[i] == 0, styles[i] == 3))

# Clue 20:
# "The person residing in a Victorian house is in the fifth house."
# (Victorian = style index 2; fifth house = index 4)
solver.add(styles[4] == 2)

# Solve the puzzle.
if solver.check() == sat:
    model = solver.model()
    solution_rows = []
    for i in range(num_houses):
        house_number = str(i + 1)
        # Get the solved integer value for each attribute.
        name_val   = model.evaluate(names[i]).as_long()
        hobby_val  = model.evaluate(hobbies[i]).as_long()
        sport_val  = model.evaluate(sports[i]).as_long()
        style_val  = model.evaluate(styles[i]).as_long()
        child_val  = model.evaluate(children[i]).as_long()
        height_val = model.evaluate(heights[i]).as_long()
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
    
    result = {
        "solution": {
            "header": ["House", "Name", "Hobby", "FavoriteSport", "HouseStyle", "Children", "Height"],
            "rows": solution_rows
        }
    }
    print(json.dumps(result, indent=2))
else:
    print("No solution found")