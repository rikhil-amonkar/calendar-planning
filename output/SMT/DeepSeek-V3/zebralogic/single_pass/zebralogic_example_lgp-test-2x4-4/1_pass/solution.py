import json
from z3 import *

# Create a solver instance
s = Solver()

# Define the houses
houses = [1, 2]

# Define the attributes
names = ["Eric", "Arnold"]
house_styles = ["victorian", "colonial"]
heights = ["very short", "short"]
educations = ["associate", "high school"]

# Create variables for each attribute in each house
name = {h: String(f"name_{h}") for h in houses}
house_style = {h: String(f"house_style_{h}") for h in houses}
height = {h: String(f"height_{h}") for h in houses}
education = {h: String(f"education_{h}") for h in houses}

# Add constraints for uniqueness
s.add(Distinct([name[h] for h in houses]))
s.add(Distinct([house_style[h] for h in houses]))
s.add(Distinct([height[h] for h in houses]))
s.add(Distinct([education[h] for h in houses]))

# Each attribute must be one of the allowed values
for h in houses:
    s.add(Or([name[h] == n for n in names]))
    s.add(Or([house_style[h] == hs for hs in house_styles]))
    s.add(Or([height[h] == ht for ht in heights]))
    s.add(Or([education[h] == e for e in educations]))

# Clue 1: The person who is short is directly left of Eric.
# This means the short person is in house 1, and Eric is in house 2.
s.add(height[1] == "short")
s.add(name[2] == "Eric")

# Clue 2: The person residing in a Victorian house is in the first house.
s.add(house_style[1] == "victorian")

# Clue 3: The person who is short is the person with an associate's degree.
s.add(education[1] == "associate")

# Check if the problem is satisfiable
if s.check() == sat:
    model = s.model()
    
    # Prepare the solution
    solution = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Height", "Education"],
            "rows": []
        }
    }
    
    for h in houses:
        row = [
            str(h),
            model.eval(name[h]).as_string(),
            model.eval(house_style[h]).as_string(),
            model.eval(height[h]).as_string(),
            model.eval(education[h]).as_string()
        ]
        solution["solution"]["rows"].append(row)
    
    # Convert to JSON and print
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")