from z3 import *
import json

# Define EnumSorts
NameSort, (Eric, Arnold) = EnumSort('Name', ['Eric', 'Arnold'])
ChildSort, (Bella, Fred) = EnumSort('Child', ['Bella', 'Fred'])
FoodSort, (GrilledCheese, Pizza) = EnumSort('Food', ['grilled_cheese', 'pizza'])

# Variables for house 1 and 2
name1, name2 = Consts('name1 name2', NameSort)
child1, child2 = Consts('child1 child2', ChildSort)
food1, food2 = Consts('food1 food2', FoodSort)

solver = Solver()

# Uniqueness constraints
solver.add(Distinct(name1, name2))
solver.add(Distinct(child1, child2))
solver.add(Distinct(food1, food2))

# Clue 1: Arnold's food is pizza
solver.add(If(name1 == Arnold, food1 == Pizza, True))
solver.add(If(name2 == Arnold, food2 == Pizza, True))

# Clue 2: The grilled cheese lover is directly left of the person whose child is Fred
solver.add(food1 == GrilledCheese)
solver.add(child2 == Fred)

if solver.check() == sat:
    model = solver.model()
    # Extract values and convert to strings
    h1 = [1, str(model[name1]), str(model[child1]), str(model[food1])]
    h2 = [2, str(model[name2]), str(model[child2]), str(model[food2])]
    solution = {
        "solution": {
            "header": ["House", "Name", "Children", "Food"],
            "rows": [h1, h2]
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")