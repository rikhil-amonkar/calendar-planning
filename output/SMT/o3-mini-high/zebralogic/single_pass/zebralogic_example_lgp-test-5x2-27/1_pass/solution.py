from z3 import *
import json

# Define our enumeration mappings.
# For names, we use:
# 0 -> Peter, 1 -> Alice, 2 -> Bob, 3 -> Eric, 4 -> Arnold
# For heights, we use:
# 0 -> very tall, 1 -> average, 2 -> tall, 3 -> very short, 4 -> short

name_labels = {0: "Peter", 1: "Alice", 2: "Bob", 3: "Eric", 4: "Arnold"}
height_labels = {0: "very tall", 1: "average", 2: "tall", 3: "very short", 4: "short"}

# There are 5 houses, indexed 0 to 4 corresponding to houses 1-5.
houses = list(range(5))

# Create Z3 integer arrays for names and heights.
names = [Int(f"name_{i}") for i in houses]
heights = [Int(f"height_{i}") for i in houses]

s = Solver()

# Domain constraints: each name and height variable must be in the correct range.
for i in houses:
    s.add(And(names[i] >= 0, names[i] <= 4))
    s.add(And(heights[i] >= 0, heights[i] <= 4))

# Each house has a unique person and a unique height.
s.add(Distinct(names))
s.add(Distinct(heights))

# Clue 1: The person who is short is in the second house.
# House 2 (index 1) has height 'short' which we mapped to 4.
s.add(heights[1] == 4)

# Clue 7: The person who has an average height is in the fifth house.
# House 5 (index 4) must have height 'average' which is 1.
s.add(heights[4] == 1)
# And ensure that no other house gets 'average'.
for i in range(4):
    s.add(heights[i] != 1)

# Clue 2: Peter is directly left of Bob.
# That means that in some house i (i from 0 to 3) if the person is Peter (0),
# then the house immediately to its right (i+1) must be Bob (2).
for i in range(4):
    s.add(Implies(names[i] == 0, names[i+1] == 2))
# Also, Peter cannot be in the rightmost house.
s.add(names[4] != 0)

# Clue 3: Eric is somewhere to the left of Peter.
# For any indices i and j, if house i is Eric (3) and house j is Peter (0) then i < j.
for i in houses:
    for j in houses:
        s.add(Implies(And(names[i] == 3, names[j] == 0), i < j))

# Clue 4: The person who is very tall is directly left of Peter.
# That means if a house (with index i, i>=1) has Peter, then the house immediately to its left (i-1) must have height very tall (0).
# Also, Peter cannot be in the first house.
s.add(names[0] != 0)
for i in range(1, 5):
    s.add(Implies(names[i] == 0, heights[i-1] == 0))

# Clue 5: Alice is directly left of the person who has an average height.
# Since average height is fixed to the fifth house (index 4), the house immediately to its left,
# which is house 4 (index 3), must be Alice (1).
s.add(names[3] == 1)
# (Alternatively, one could add the implication for any house with average height,
# but here it's sufficient given Clue 7.)

# Clue 6: The person who is short and the person who is very short are next to each other.
# The short person is in house 2 (index 1). Its neighbors are house 1 (index 0) and house 3 (index 2).
# So either house 1 or house 3 must have height very short (3).
s.add(Or(heights[0] == 3, heights[2] == 3))

# Check the constraints and extract the solution.
if s.check() == sat:
    m = s.model()
    solution_rows = []
    for i in houses:
        # House numbers are 1-indexed in the output.
        house_num = str(i + 1)
        name_val = m.evaluate(names[i]).as_long()
        height_val = m.evaluate(heights[i]).as_long()
        solution_rows.append([house_num, name_labels[name_val], height_labels[height_val]])
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Height"],
            "rows": solution_rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")