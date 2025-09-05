from z3 import *
import json

# Create the solver
solver = Solver()

houses = 5

# Create variables for each house for Name, Mother, and Height.
names = [Int(f"name_{i}") for i in range(houses)]
mothers = [Int(f"mother_{i}") for i in range(houses)]
heights = [Int(f"height_{i}") for i in range(houses)]

# Domain constraints: each variable is in the range 0 to 4.
for i in range(houses):
    solver.add(names[i] >= 0, names[i] < 5)
    solver.add(mothers[i] >= 0, mothers[i] < 5)
    solver.add(heights[i] >= 0, heights[i] < 5)

# All values in each category must be distinct.
solver.add(Distinct(names))
solver.add(Distinct(mothers))
solver.add(Distinct(heights))

# Mapping for our codes:
# Names: 0: Eric, 1: Peter, 2: Arnold, 3: Alice, 4: Bob
# Mothers: 0: Kailyn, 1: Janelle, 2: Aniya, 3: Penny, 4: Holly
# Heights: 0: average, 1: very short, 2: short, 3: very tall, 4: tall

# Clue 1: "Alice is The person whose mother's name is Aniya."
for i in range(houses):
    solver.add(Implies(names[i] == 3, mothers[i] == 2))
    solver.add(Implies(mothers[i] == 2, names[i] == 3))

# Clue 2: "The person who has an average height is somewhere to the left of The person whose mother's name is Penny."
for i in range(houses):
    for j in range(houses):
        solver.add(Implies(And(heights[i] == 0, mothers[j] == 3), i < j))

# Clue 3: "The person whose mother's name is Janelle is Bob."
for i in range(houses):
    solver.add(Implies(mothers[i] == 1, names[i] == 4))
    solver.add(Implies(names[i] == 4, mothers[i] == 1))

# Clue 4: "Peter is not in the second house."
solver.add(names[1] != 1)

# Clue 5: "The person who is short is directly left of Arnold."
solver.add(
    Or(
        And(heights[0] == 2, names[1] == 2),
        And(heights[1] == 2, names[2] == 2),
        And(heights[2] == 2, names[3] == 2),
        And(heights[3] == 2, names[4] == 2)
    )
)

# Clue 6: "The person who is very tall is Arnold."
for i in range(houses):
    solver.add(Implies(heights[i] == 3, names[i] == 2))
    solver.add(Implies(names[i] == 2, heights[i] == 3))

# Clue 7: "Bob is directly left of the person who has an average height."
solver.add(
    Or(
        And(names[0] == 4, heights[1] == 0),
        And(names[1] == 4, heights[2] == 0),
        And(names[2] == 4, heights[3] == 0),
        And(names[3] == 4, heights[4] == 0)
    )
)

# Clue 8: "Eric is not in the fifth house."
solver.add(names[4] != 0)

# Clue 9: "The person who is very tall is somewhere to the right of The person whose mother's name is Holly."
for i in range(houses):
    for j in range(houses):
        solver.add(Implies(And(mothers[i] == 4, heights[j] == 3), i < j))

# Clue 10: "Eric is The person whose mother's name is Kailyn."
for i in range(houses):
    solver.add(Implies(names[i] == 0, mothers[i] == 0))
    solver.add(Implies(mothers[i] == 0, names[i] == 0))

# Clue 11: "The person who is very short is in the fifth house."
solver.add(heights[4] == 1)

# Define the mapping dictionaries for final output.
namesMap = {0: "Eric", 1: "Peter", 2: "Arnold", 3: "Alice", 4: "Bob"}
mothersMap = {0: "Kailyn", 1: "Janelle", 2: "Aniya", 3: "Penny", 4: "Holly"}
heightsMap = {0: "average", 1: "very short", 2: "short", 3: "very tall", 4: "tall"}

# Solve and build the solution output
if solver.check() == sat:
    model = solver.model()
    solution_rows = []
    for i in range(houses):
        house_number = str(i + 1)
        name_val = model[names[i]].as_long()
        mother_val = model[mothers[i]].as_long()
        height_val = model[heights[i]].as_long()
        solution_rows.append([
            house_number,
            namesMap[name_val],
            mothersMap[mother_val],
            heightsMap[height_val]
        ])
    output = {
        "solution": {
            "header": ["House", "Name", "Mother", "Height"],
            "rows": solution_rows
        }
    }
else:
    output = {
        "solution": {
            "header": ["House", "Name", "Mother", "Height"],
            "rows": []
        }
    }

print(json.dumps(output, indent=2))