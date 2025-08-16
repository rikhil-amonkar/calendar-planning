import json
from z3 import *

# Initialize the solver
solver = Solver()

# Define the houses
houses = [1, 2, 3, 4, 5, 6]

# Define the attributes
names = ["Bob", "Peter", "Eric", "Alice", "Arnold", "Carol"]
hair_colors = ["auburn", "blonde", "brown", "black", "red", "gray"]
heights = ["very tall", "average", "very short", "tall", "super tall", "short"]

# Create variables for each attribute in each house
name_vars = {house: Int(f"name_{house}") for house in houses}
hair_vars = {house: Int(f"hair_{house}") for house in houses}
height_vars = {house: Int(f"height_{house}") for house in houses}

# Add constraints to ensure each attribute is unique within its category
for house in houses:
    solver.add(And(name_vars[house] >= 0, name_vars[house] < len(names)))
    solver.add(And(hair_vars[house] >= 0, hair_vars[house] < len(hair_colors)))
    solver.add(And(height_vars[house] >= 0, height_vars[house] < len(heights)))

solver.add(Distinct([name_vars[house] for house in houses]))
solver.add(Distinct([hair_vars[house] for house in houses]))
solver.add(Distinct([height_vars[house] for house in houses]))

# Clue 2: Alice is in the fourth house.
alice_index = names.index("Alice")
solver.add(name_vars[4] == alice_index)

# Clue 8: The person who has blonde hair is Carol.
carol_index = names.index("Carol")
blonde_index = hair_colors.index("blonde")
for house in houses:
    solver.add(Implies(hair_vars[house] == blonde_index, name_vars[house] == carol_index))

# Clue 1: The person who has blonde hair is directly left of Bob.
bob_index = names.index("Bob")
for house in range(1, 6):
    solver.add(Implies(hair_vars[house] == blonde_index, name_vars[house + 1] == bob_index))

# Clue 11: Bob is the person who has brown hair.
brown_index = hair_colors.index("brown")
for house in houses:
    solver.add(Implies(name_vars[house] == bob_index, hair_vars[house] == brown_index))

# Clue 6: The person who has red hair is Eric.
eric_index = names.index("Eric")
red_index = hair_colors.index("red")
for house in houses:
    solver.add(Implies(hair_vars[house] == red_index, name_vars[house] == eric_index))

# Clue 12: The person who has gray hair is in the third house.
gray_index = hair_colors.index("gray")
solver.add(hair_vars[3] == gray_index)

# Clue 9: There is one house between the person who has gray hair and the person who has red hair.
# Gray is in house 3, so red must be in house 5 (since 3 + 2 = 5)
solver.add(hair_vars[5] == red_index)

# Clue 5: The person who has black hair is not in the fourth house.
black_index = hair_colors.index("black")
solver.add(hair_vars[4] != black_index)

# Clue 3: The person who is short is Arnold.
arnold_index = names.index("Arnold")
short_index = heights.index("short")
for house in houses:
    solver.add(Implies(height_vars[house] == short_index, name_vars[house] == arnold_index))

# Clue 4: The person who is tall is in the sixth house.
tall_index = heights.index("tall")
solver.add(height_vars[6] == tall_index)

# Clue 10: The person who is very short is in the fifth house.
very_short_index = heights.index("very short")
solver.add(height_vars[5] == very_short_index)

# Clue 7: The person who is super tall is somewhere to the right of the person who has an average height.
average_index = heights.index("average")
super_tall_index = heights.index("super tall")
for house in houses:
    for other_house in range(house + 1, 7):
        solver.add(Implies(height_vars[house] == average_index, height_vars[other_house] == super_tall_index))

# Clue 13: The person who has blonde hair is the person who is very tall.
very_tall_index = heights.index("very tall")
for house in houses:
    solver.add(Implies(hair_vars[house] == blonde_index, height_vars[house] == very_tall_index))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "HairColor", "Height"],
            "rows": []
        }
    }
    for house in houses:
        name = names[model.evaluate(name_vars[house]).as_long()]
        hair = hair_colors[model.evaluate(hair_vars[house]).as_long()]
        height = heights[model.evaluate(height_vars[house]).as_long()]
        solution["solution"]["rows"].append([str(house), name, hair, height])
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")