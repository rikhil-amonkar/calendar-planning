import json
import itertools

def all_bijections(houses, values):
    for perm in itertools.permutations(values, len(houses)):
        yield {house: val for house, val in zip(houses, perm)}

def house_of_value(mapping, target_value):
    for house, val in mapping.items():
        if val == target_value:
            return house
    return None

def solve():
    # Input variables
    houses = [1, 2]  # House numbers from left (1) to right (2)
    names = ["Eric", "Arnold"]
    house_styles = ["victorian", "colonial"]

    # Constraints
    def name_constraints(mapping):
        # 2. Eric is in the first house.
        return mapping[1] == "Eric"

    def style_constraints(mapping):
        # 1. The person residing in a Victorian house is somewhere to the left
        #    of the person living in a colonial-style house.
        v_house = house_of_value(mapping, "victorian")
        c_house = house_of_value(mapping, "colonial")
        return v_house is not None and c_house is not None and v_house < c_house

    # Compute all valid mappings for names and house styles independently
    valid_name_mappings = [m for m in all_bijections(houses, names) if name_constraints(m)]
    valid_style_mappings = [m for m in all_bijections(houses, house_styles) if style_constraints(m)]

    # Combine to form complete solutions (no cross-attribute constraints needed here)
    solutions = []
    for nm in valid_name_mappings:
        for sm in valid_style_mappings:
            # Construct rows per house
            rows = []
            for h in sorted(houses):
                rows.append([str(h), nm[h], sm[h]])
            solutions.append(rows)

    # Ensure there is at least one solution
    if not solutions:
        raise ValueError("No solution found with the given constraints.")

    # If multiple, choose the first (should be unique for this puzzle)
    rows = solutions[0]

    output = {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": rows
        }
    }
    print(json.dumps(output, ensure_ascii=False))