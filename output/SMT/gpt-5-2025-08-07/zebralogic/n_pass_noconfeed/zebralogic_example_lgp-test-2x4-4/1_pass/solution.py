import json
import re
from z3 import Solver, Int, And, Distinct, sat

def sanitize_var_name(prefix, label):
    return f"{prefix}_{re.sub(r'[^A-Za-z0-9_]', '_', label.replace(' ', '_'))}"

def create_category_vars(values, prefix, num_houses):
    vars_dict = {}
    for val in values:
        vars_dict[val] = Int(sanitize_var_name(prefix, val))
    # Domain constraints
    for v in vars_dict.values():
        solver.add(And(v >= 1, v <= num_houses))
    # All different (bijection to houses)
    solver.add(Distinct(list(vars_dict.values())))
    return vars_dict

def invert_mapping(category_vars, model):
    mapping = {}
    for value, var in category_vars.items():
        h = model.evaluate(var).as_long()
        mapping[h] = value
    return mapping

# Problem data
houses = [1, 2]
names = ["Eric", "Arnold"]
house_styles = ["victorian", "colonial"]
heights = ["very short", "short"]
educations = ["associate", "high school"]

# Initialize solver
solver = Solver()

# Create variables for each category: maps attribute value -> house index
name_pos = create_category_vars(names, "pos_name", len(houses))
style_pos = create_category_vars(house_styles, "pos_style", len(houses))
height_pos = create_category_vars(heights, "pos_height", len(houses))
education_pos = create_category_vars(educations, "pos_education", len(houses))

# Clues as constraints
# 1. The person who is short is directly left of Eric.
solver.add(height_pos["short"] + 1 == name_pos["Eric"])

# 2. The person residing in a Victorian house is in the first house.
solver.add(style_pos["victorian"] == 1)

# 3. The person who is short is the person with an associate's degree.
solver.add(height_pos["short"] == education_pos["associate"])

# Solve
if solver.check() != sat:
    # In the unlikely event the puzzle is unsatisfiable, output an empty structure
    result = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Height", "Education"],
            "rows": [[str(h), "", "", "", ""] for h in houses]
        }
    }
    print(json.dumps(result, indent=2))
else:
    model = solver.model()

    # Invert mappings to get attribute per house
    name_by_house = invert_mapping(name_pos, model)
    style_by_house = invert_mapping(style_pos, model)
    height_by_house = invert_mapping(height_pos, model)
    education_by_house = invert_mapping(education_pos, model)

    rows = []
    for h in houses:
        rows.append([
            str(h),
            name_by_house[h],
            style_by_house[h],
            height_by_house[h],
            education_by_house[h]
        ])

    result = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Height", "Education"],
            "rows": rows
        }
    }

    print(json.dumps(result, indent=2))