from z3 import *
import json

# Initialize solver
solver = Solver()

# Define enums for names and foods
Names = EnumSort('Names', ['Alice', 'Bob', 'Charlie', 'David', 'Eve'])
Foods = EnumSort('Foods', ['Pizza', 'Sushi', 'Burger', 'Pasta', 'Tacos'])

# Create variables for each house
names = Consts('names_0 names_1 names_2 names_3 names_4', Names)
foods = Consts('foods_0 foods_1 foods_2 foods_3 foods_4', Foods)
heights = Ints('heights_0 heights_1 heights_2 heights_3 heights_4')

# Add constraints: all values must be distinct
solver.add(Distinct(names))
solver.add(Distinct(foods))
solver.add(Distinct(heights))

# Add constraints: heights are between 1 and 5
for h in heights:
    solver.add(And(h >= 1, h <= 5))

# Example clues (replace with actual puzzle constraints)
# 1. Alice lives in the first house
solver.add(names[0] == Names.Alice)

# 2. Bob is taller than Charlie
solver.add(heights[1] > heights[2])

# 3. The person who eats Pizza lives in house 3
solver.add(foods[2] == Foods.Pizza)

# Add more constraints here as needed for your logic puzzle

# Check for solution
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Height", "Food"],
            "rows": []
        }
    }
    for i in range(5):
        house_num = i + 1
        name_val = model.eval(names[i]).decl().name()
        height_val = model.eval(heights[i]).as_string()
        food_val = model.eval(foods[i]).decl().name()
        solution["solution"]["rows"].append([str(house_num), name_val, height_val, food_val])
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")