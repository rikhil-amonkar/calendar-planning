import z3
import json

# Create EnumSorts for each attribute
name_sort, (arnold, eric) = z3.EnumSort('Name', ['Arnold', 'Eric'])
food_sort, (grilled_cheese, pizza) = z3.EnumSort('Food', ['grilled cheese', 'pizza'])
mother_sort, (holly, aniya) = z3.EnumSort('Mother', ['Holly', 'Aniya'])

# Variables for house 1 and house 2
name1 = z3.Const('name1', name_sort)
food1 = z3.Const('food1', food_sort)
mother1 = z3.Const('mother1', mother_sort)

name2 = z3.Const('name2', name_sort)
food2 = z3.Const('food2', food_sort)
mother2 = z3.Const('mother2', mother_sort)

# Create solver and add constraints
solver = z3.Solver()

# Each category must have unique values between houses
solver.add(name1 != name2)
solver.add(food1 != food2)
solver.add(mother1 != mother2)

# Clue 1: Grilled cheese is directly left of pizza
solver.add(food1 == grilled_cheese)
solver.add(food2 == pizza)

# Clue 2: Arnold is not in the second house
solver.add(name2 == eric)

# Clue 3: Arnold's mother is Holly
solver.add(mother1 == holly)

# Check for solution
if solver.check() == z3.sat:
    model = solver.model()
    
    # Extract values for house 1
    h1_name = str(model.eval(name1))
    h1_food = str(model.eval(food1))
    h1_mother = str(model.eval(mother1))
    
    # Extract values for house 2
    h2_name = str(model.eval(name2))
    h2_food = str(model.eval(food2))
    h2_mother = str(model.eval(mother2))
    
    # Build solution dictionary
    solution = {
        "solution": {
            "header": ["House", "Name", "Food", "Mother"],
            "rows": [
                ["1", h1_name, h1_food, h1_mother],
                ["2", h2_name, h2_food, h2_mother]
            ]
        }
    }
    
    # Output as JSON
    print(json.dumps(solution, indent=2))
else:
    print(json.dumps({"error": "No solution found"}))