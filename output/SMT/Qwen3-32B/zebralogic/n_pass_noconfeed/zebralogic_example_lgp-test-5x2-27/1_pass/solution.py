from z3 import *
import json

# Define variables for each house (1-5)
n1, n2, n3, n4, n5 = Ints('n1 n2 n3 n4 n5')  # names
h1, h2, h3, h4, h5 = Ints('h1 h2 h3 h4 h5')  # heights

s = Solver()

# All names are distinct
s.add(Distinct(n1, n2, n3, n4, n5))
# All heights are distinct
s.add(Distinct(h1, h2, h3, h4, h5))

# Clue 1: The person who is short is in the second house.
s.add(h2 == 4)  # short is index 4

# Clue 7: The person who is average is in the fifth house.
s.add(h5 == 1)  # average is index 1

# Clue 6: The person who is short and the person who is very short are next to each other.
s.add(Or(h1 == 3, h3 == 3))  # very short is index 3

# Clue 5: Alice is directly left of the person who has an average height.
s.add(n4 == 1)  # Alice is index 1 and house 4

# Clue 2: Peter is directly left of Bob.
s.add(Or(
    And(n1 == 0, n2 == 2),
    And(n2 == 0, n3 == 2),
    And(n3 == 0, n4 == 2),
    And(n4 == 0, n5 == 2)
))  # Peter is index 0, Bob is index 2

# Clue 4: The person who is very tall is directly left of Peter.
s.add(Or(
    And(h1 == 0, n2 == 0),
    And(h2 == 0, n3 == 0),
    And(h3 == 0, n4 == 0),
    And(h4 == 0, n5 == 0)
))  # very tall is index 0

# Clue 3: Eric is somewhere to the left of Peter.
s.add(Or(
    And(n1 == 3, Or(n2 == 0, n3 == 0, n4 == 0, n5 == 0)),
    And(n2 == 3, Or(n3 == 0, n4 == 0, n5 == 0)),
    And(n3 == 3, Or(n4 == 0, n5 == 0)),
    And(n4 == 3, n5 == 0)
))  # Eric is index 3, Peter is index 0

# Ensure variables are within 0-4 range
for var in [n1, n2, n3, n4, n5, h1, h2, h3, h4, h5]:
    s.add(And(0 <= var, var <= 4))

if s.check() == sat:
    model = s.model()
    names_list = ["Peter", "Alice", "Bob", "Eric", "Arnold"]
    heights_list = ["very tall", "average", "tall", "very short", "short"]
    rows = []
    for i in range(1, 6):
        ni = model.eval(Int(f"n{i}")).as_long()
        hi = model.eval(Int(f"h{i}")).as_long()
        house_num = str(i)
        name = names_list[ni]
        height = heights_list[hi]
        rows.append([house_num, name, height])
    solution = {
        "solution": {
            "header": ["House", "Name", "Height"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")