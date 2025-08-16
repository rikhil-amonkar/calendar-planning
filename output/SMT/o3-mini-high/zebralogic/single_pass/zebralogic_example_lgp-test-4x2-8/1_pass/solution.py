from z3 import *
import json

# Define constants for names
PETER = 0
ARNOLD = 1
ALICE = 2
ERIC = 3

# Define constants for colors
YELLOW = 0
GREEN = 1
RED = 2
WHITE = 3

# Create 4 houses (using 0-indexing: house 1 is index 0, etc.)
names = [Int(f"names_{i}") for i in range(4)]
colors = [Int(f"colors_{i}") for i in range(4)]

s = Solver()

# Each house's name and color must be in the proper domain (0..3)
for i in range(4):
    s.add(And(names[i] >= 0, names[i] <= 3))
    s.add(And(colors[i] >= 0, colors[i] <= 3))

# All houses must have distinct names and distinct colors.
s.add(Distinct(names))
s.add(Distinct(colors))

# Clue 1: The person whose favorite color is green is in the third house.
# (Third house is index 2)
s.add(colors[2] == GREEN)

# Clue 2: Peter is in the first house.
# (First house is index 0)
s.add(names[0] == PETER)

# Clue 3: There is one house between the person whose favorite color is red and the person who loves yellow.
# Since colors are unique, for any house i with red and any house j with yellow, |i - j| must equal 2.
for i in range(4):
    for j in range(4):
        s.add(Implies(And(colors[i] == RED, colors[j] == YELLOW), Abs(i - j) == 2))

# Clue 4: Arnold is directly left of Eric.
# That is, for one of the houses 1-3 (indexes 0 to 2), if house[i] is Arnold then house[i+1] is Eric.
s.add(Or(
    And(names[0] == ARNOLD, names[1] == ERIC),
    And(names[1] == ARNOLD, names[2] == ERIC),
    And(names[2] == ARNOLD, names[3] == ERIC)
))

# Clue 5: Eric is the person who loves yellow.
# For each house, if the occupant is Eric then its color must be yellow.
for i in range(4):
    s.add(Implies(names[i] == ERIC, colors[i] == YELLOW))

# Solve the puzzle
if s.check() == sat:
    m = s.model()
    # Mapping from constant integers to names and colors
    name_map = {PETER: "Peter", ARNOLD: "Arnold", ALICE: "Alice", ERIC: "Eric"}
    color_map = {YELLOW: "yellow", GREEN: "green", RED: "red", WHITE: "white"}
    
    rows = []
    for i in range(4):
        house_number = str(i + 1)
        name_val = m[names[i]].as_long()
        color_val = m[colors[i]].as_long()
        rows.append([house_number, name_map[name_val], color_map[color_val]])
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Color"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")