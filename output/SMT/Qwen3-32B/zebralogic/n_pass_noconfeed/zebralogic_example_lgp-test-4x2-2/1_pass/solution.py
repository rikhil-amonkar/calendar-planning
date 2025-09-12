from z3 import *
import json

# Define Z3 integer variables for each house's name and style
name = [Int(f'name_{i}') for i in range(1, 5)]
style = [Int(f'style_{i}') for i in range(1, 5)]

s = Solver()

# Add constraints for distinct names and styles
s.add(Distinct(name[0], name[1], name[2], name[3]))
s.add(Distinct(style[0], style[1], style[2], style[3]))

# Domain constraints: each variable must be between 0 and 3
for n in name + style:
    s.add(And(n >= 0, n <= 3))

# Add specific constraints based on the puzzle clues
# Clue 3: Eric is in the third house (index 2) => name[2] = 2
s.add(name[2] == 2)
# Clue 4: Arnold is in the fourth house (index 3) => name[3] = 0
s.add(name[3] == 0)
# Clue 1: Eric's house is Craftsman-style => style[2] = 3
s.add(style[2] == 3)
# Clue 5: The person in the Victorian house is Alice
for i in range(4):
    s.add(Implies(style[i] == 0, name[i] == 3))
# Clue 2: Ranch is directly left of Victorian
s.add(Or(
    And(style[0] == 1, style[1] == 0),
    And(style[1] == 1, style[2] == 0),
    And(style[2] == 1, style[3] == 0)
))

if s.check() == sat:
    model = s.model()
    # Mapping from integer values to names and styles
    name_map = {0: 'Arnold', 1: 'Peter', 2: 'Eric', 3: 'Alice'}
    style_map = {0: 'victorian', 1: 'ranch', 2: 'colonial', 3: 'craftsman'}
    rows = []
    for i in range(4):
        house_num = i + 1
        current_name = model[name[i]].as_long()
        current_style = model[style[i]].as_long()
        rows.append([str(house_num), name_map[current_name], style_map[current_style]])
    solution = {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")