from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
houses = range(1, 7)
names = ["Bob", "Peter", "Eric", "Alice", "Arnold", "Carol"]
hair_colors = ["auburn", "blonde", "brown", "black", "red", "gray"]
heights = ["very tall", "average", "very short", "tall", "super tall", "short"]

# Create dictionaries to map each attribute to a variable
name_vars = {name: Int(f'name_{name}') for name in names}
hair_color_vars = {color: Int(f'hair_color_{color}') for color in hair_colors}
height_vars = {height: Int(f'height_{height}') for height in heights}

# Add constraints for each attribute to be unique and within the range of houses
for var_dict in [name_vars, hair_color_vars, height_vars]:
    solver.add(Distinct(var_dict.values()))
    for var in var_dict.values():
        solver.add(And(var >= 1, var <= 6))

# Clue 1: The person who has blonde hair is directly left of Bob.
solver.add(hair_color_vars["blonde"] + 1 == name_vars["Bob"])

# Clue 2: Alice is in the fourth house.
solver.add(name_vars["Alice"] == 4)

# Clue 3: The person who is short is Arnold.
solver.add(height_vars["short"] == name_vars["Arnold"])

# Clue 4: The person who is tall is in the sixth house.
solver.add(height_vars["tall"] == 6)

# Clue 5: The person who has black hair is not in the fourth house.
solver.add(hair_color_vars["black"] != 4)

# Clue 6: The person who has red hair is Eric.
solver.add(hair_color_vars["red"] == name_vars["Eric"])

# Clue 7: The person who is super tall is somewhere to the right of the person who has an average height.
solver.add(height_vars["super tall"] > height_vars["average"])

# Clue 8: The person who has blonde hair is Carol.
solver.add(hair_color_vars["blonde"] == name_vars["Carol"])

# Clue 9: There is one house between the person who has gray hair and the person who has red hair.
solver.add(Abs(hair_color_vars["gray"] - hair_color_vars["red"]) == 2)

# Clue 10: The person who is very short is in the fifth house.
solver.add(height_vars["very short"] == 5)

# Clue 11: Bob is the person who has brown hair.
solver.add(hair_color_vars["brown"] == name_vars["Bob"])

# Clue 12: The person who has gray hair is in the third house.
solver.add(hair_color_vars["gray"] == 3)

# Clue 13: The person who has blonde hair is the person who is very tall.
solver.add(hair_color_vars["blonde"] == height_vars["very tall"])

# Check if the solution exists
if solver.check() == sat:
    model = solver.model()
    
    # Prepare the result in the required format
    result = {
        "solution": {
            "header": ["House", "Name", "HairColor", "Height"],
            "rows": []
        }
    }
    
    # Extract the solution
    for house in houses:
        name = next(name for name, var in name_vars.items() if model.evaluate(var) == house).as_string()[1:-1]
        hair_color = next(color for color, var in hair_color_vars.items() if model.evaluate(var) == house).as_string()[1:-1]
        height = next(height for height, var in height_vars.items() if model.evaluate(var) == house).as_string()[1:-1]
        result["solution"]["rows"].append([str(house), name, hair_color, height])
    
    # Print the result as JSON
    import json
    print(json.dumps(result, indent=2))
else:
    print("No solution found")