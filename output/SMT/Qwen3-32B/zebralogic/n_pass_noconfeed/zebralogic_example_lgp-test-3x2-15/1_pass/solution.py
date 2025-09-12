from z3 import *
import json

# Define EnumSorts for names and heights
Name, (Arnold, Peter, Eric) = EnumSort('Name', ['Arnold', 'Peter', 'Eric'])
Height, (Short, Average, VeryShort) = EnumSort('Height', ['short', 'average', 'very short'])

# Create variables for each house's name and height
name = [Const(f'name_{i+1}', Name) for i in range(3)]
height = [Const(f'height_{i+1}', Height) for i in range(3)]

s = Solver()

# Add distinctness constraints
s.add(Distinct(name[0], name[1], name[2]))
s.add(Distinct(height[0], height[1], height[2]))

# Person house variables
eric_house = Int('eric_house')
peter_house = Int('peter_house')
arnold_house = Int('arnold_house')

# Height house variables
very_short_house = Int('very_short_house')

# Link person variables to their house numbers
for i in range(3):
    house_num = i + 1
    s.add(Implies(name[i] == Eric, eric_house == house_num))
    s.add(Implies(name[i] == Peter, peter_house == house_num))
    s.add(Implies(name[i] == Arnold, arnold_house == house_num))

# Link very_short_house to the house with VeryShort height
for i in range(3):
    house_num = i + 1
    s.add(Implies(height[i] == VeryShort, very_short_house == house_num))

# Add puzzle constraints
s.add(height[0] == Short)  # Clue 2: short is in the first house
s.add(peter_house > eric_house)  # Clue 1: Peter is to the right of Eric
s.add(Abs(1 - very_short_house) == 2)  # Clue 3: one house between short and very short
s.add(Abs(arnold_house - very_short_house) == 1)  # Clue 4: Arnold and very short are adjacent

if s.check() == sat:
    model = s.model()
    rows = []
    for i in range(3):
        house_num = i + 1
        name_val = model[name[i]].decl().name()
        height_val = model[height[i]].decl().name()
        rows.append([str(house_num), name_val, height_val])
    solution = {
        "solution": {
            "header": ["House", "Name", "Height"],
            "rows": rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")