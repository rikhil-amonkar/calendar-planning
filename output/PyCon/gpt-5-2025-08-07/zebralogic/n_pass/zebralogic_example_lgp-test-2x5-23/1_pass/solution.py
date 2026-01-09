import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    # Define houses
    houses = [1, 2]

    # Define attributes
    names = ["Arnold", "Eric"]
    educations = ["associate", "high school"]
    heights = ["short", "very short"]
    foods = ["grilled cheese", "pizza"]
    drinks = ["tea", "water"]

    problem = Problem()

    # Create variables for each attribute value representing the house number it is assigned to
    # Prefix variables with category names to avoid collisions
    var_names = {
        "Name": [f"Name:{v}" for v in names],
        "Education": [f"Education:{v}" for v in educations],
        "Height": [f"Height:{v}" for v in heights],
        "Food": [f"Food:{v}" for v in foods],
        "Drink": [f"Drink:{v}" for v in drinks],
    }

    # Add variables with domain = houses
    for category_vars in var_names.values():
        for var in category_vars:
            problem.addVariable(var, houses)

    # AllDifferent constraints within each category
    problem.addConstraint(AllDifferentConstraint(), var_names["Name"])
    problem.addConstraint(AllDifferentConstraint(), var_names["Education"])
    problem.addConstraint(AllDifferentConstraint(), var_names["Height"])
    problem.addConstraint(AllDifferentConstraint(), var_names["Food"])
    problem.addConstraint(AllDifferentConstraint(), var_names["Drink"])

    # Clues as constraints:
    # 1. The person who is very short is the person who is a pizza lover.
    problem.addConstraint(
        lambda hv, fp: hv == fp,
        (f"Height:very short", f"Food:pizza")
    )

    # 2. The person who loves eating grilled cheese is in the second house.
    problem.addConstraint(lambda x: x == 2, (f"Food:grilled cheese",))

    # 3. The person with a high school diploma is the person who is a pizza lover.
    problem.addConstraint(
        lambda eh, fp: eh == fp,
        (f"Education:high school", f"Food:pizza")
    )

    # 4. The tea drinker is the person who loves eating grilled cheese.
    problem.addConstraint(
        lambda dt, fg: dt == fg,
        (f"Drink:tea", f"Food:grilled cheese")
    )

    # 5. Arnold is the person who is a pizza lover.
    problem.addConstraint(
        lambda na, fp: na == fp,
        (f"Name:Arnold", f"Food:pizza")
    )

    solutions = problem.getSolutions()
    if not solutions:
        raise ValueError("No solution found for the given puzzle.")

    sol = solutions[0]

    # Helper to find which value in a category is at a given house
    def value_at_house(category, values, house):
        for v in values:
            if sol[f"{category}:{v}"] == house:
                return v
        return None

    rows = []
    for house in houses:
        row = [
            str(house),
            value_at_house("Name", names, house),
            value_at_house("Education", educations, house),
            value_at_house("Height", heights, house),
            value_at_house("Food", foods, house),
            value_at_house("Drink", drinks, house),
        ]
        rows.append(row)

    result = {
        "solution": {
            "header": ["House", "Name", "Education", "Height", "Food", "Drink"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False, indent=2))