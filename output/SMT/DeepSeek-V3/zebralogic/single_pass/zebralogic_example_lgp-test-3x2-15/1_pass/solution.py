from z3 import *
import json

# Create a solver instance
s = Solver()

# Define the houses
houses = [1, 2, 3]

# Define the attributes
names = ["Arnold", "Peter", "Eric"]
heights = ["short", "average", "very short"]

# Create variables for each house's name and height
name_vars = {house: Int(f"name_{house}") for house in houses}
height_vars = {house: Int(f"height_{house}") for house in houses}

# Add constraints for names and heights to be unique and within valid ranges
for house in houses:
    s.add(And(name_vars[house] >= 0, name_vars[house] < len(names)))
    s.add(And(height_vars[house] >= 0, height_vars[house] < len(heights)))

s.add(Distinct([name_vars[house] for house in houses]))
s.add(Distinct([height_vars[house] for house in houses]))

# Clue 1: Peter is somewhere to the right of Eric
# This means the house number for Peter is greater than the house number for Eric
s.add(Exists([house_p, house_e], 
      And(house_p > house_e, 
          name_vars[house_p] == names.index("Peter"), 
          name_vars[house_e] == names.index("Eric"))))

# Clue 2: The person who is short is in the first house
s.add(height_vars[1] == heights.index("short"))

# Clue 3: There is one house between the person who is short and the person who is very short
# Since short is in house 1, very short must be in house 3 (because house 2 is one house apart)
s.add(height_vars[3] == heights.index("very short"))

# Clue 4: Arnold and the person who is very short are next to each other
# Very short is in house 3, so Arnold must be in house 2
s.add(name_vars[2] == names.index("Arnold"))

# Solve the model
if s.check() == sat:
    model = s.model()
    
    # Prepare the solution
    solution = {
        "solution": {
            "header": ["House", "Name", "Height"],
            "rows": []
        }
    }
    
    for house in houses:
        name_index = model.evaluate(name_vars[house]).as_long()
        height_index = model.evaluate(height_vars[house]).as_long()
        solution["solution"]["rows"].append([
            str(house),
            names[name_index],
            heights[height_index]
        ])
    
    # Convert to JSON
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")