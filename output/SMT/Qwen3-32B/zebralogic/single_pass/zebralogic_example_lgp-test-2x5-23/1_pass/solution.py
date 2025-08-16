import json
from z3 import *

solver = Solver()

# Define variables for each house's attributes
name_1 = String('name_1')
education_1 = String('education_1')
height_1 = String('height_1')
food_1 = String('food_1')
drink_1 = String('drink_1')

name_2 = String('name_2')
education_2 = String('education_2')
height_2 = String('height_2')
food_2 = String('food_2')
drink_2 = String('drink_2')

# Add constraints for possible values and uniqueness
# Names
solver.add(Or(name_1 == "Arnold", name_1 == "Eric"))
solver.add(Or(name_2 == "Arnold", name_2 == "Eric"))
solver.add(name_1 != name_2)

# Education
solver.add(Or(education_1 == "associate", education_1 == "high school"))
solver.add(Or(education_2 == "associate", education_2 == "high school"))
solver.add(education_1 != education_2)

# Height
solver.add(Or(height_1 == "short", height_1 == "very short"))
solver.add(Or(height_2 == "short", height_2 == "very short"))
solver.add(height_1 != height_2)

# Food
solver.add(Or(food_1 == "grilled cheese", food_1 == "pizza"))
solver.add(Or(food_2 == "grilled cheese", food_2 == "pizza"))
solver.add(food_1 != food_2)

# Drink
solver.add(Or(drink_1 == "tea", drink_1 == "water"))
solver.add(Or(drink_2 == "tea", drink_2 == "water"))
solver.add(drink_1 != drink_2)

# Add specific clues as constraints
# Clue 2: Grilled cheese in second house
solver.add(food_2 == "grilled cheese")

# Clue 5: Arnold is the pizza lover
solver.add(Implies(name_1 == "Arnold", food_1 == "pizza"))
solver.add(Implies(name_2 == "Arnold", food_2 == "pizza"))

# Clue 1: Very short person is pizza lover
solver.add(Implies(height_1 == "very short", food_1 == "pizza"))
solver.add(Implies(height_2 == "very short", food_2 == "pizza"))

# Clue 3: High school diploma person is pizza lover
solver.add(Implies(education_1 == "high school", food_1 == "pizza"))
solver.add(Implies(education_2 == "high school", food_2 == "pizza"))

# Clue 4: Tea drinker loves grilled cheese
solver.add(Implies(drink_1 == "tea", food_1 == "grilled cheese"))
solver.add(Implies(drink_2 == "tea", food_2 == "grilled cheese"))

# Check for solution
if solver.check() == sat:
    model = solver.model()
    # Extract values for house 1
    h1_name = model[name_1]
    h1_education = model[education_1]
    h1_height = model[height_1]
    h1_food = model[food_1]
    h1_drink = model[drink_1]
    
    # Extract values for house 2
    h2_name = model[name_2]
    h2_education = model[education_2]
    h2_height = model[height_2]
    h2_food = model[food_2]
    h2_drink = model[drink_2]
    
    # Convert Z3 string values to Python strings
    rows = [
        ["1", str(h1_name), str(h1_education), str(h1_height), str(h1_food), str(h1_drink)],
        ["2", str(h2_name), str(h2_education), str(h2_height), str(h2_food), str(h2_drink)]
    ]
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Education", "Height", "Food", "Drink"],
            "rows": rows
        }
    }
    
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")