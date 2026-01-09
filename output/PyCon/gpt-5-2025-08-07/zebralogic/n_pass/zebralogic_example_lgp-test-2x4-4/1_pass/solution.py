import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define categories and values
    houses = [1, 2]
    Names = ["Eric", "Arnold"]
    HouseStyles = ["victorian", "colonial"]
    Heights = ["very short", "short"]
    Educations = ["associate", "high school"]

    # Helper to create variable names
    def var_name(category, value):
        safe_value = value.replace(" ", "_")
        return f"{category}_{safe_value}"

    # Initialize problem
    problem = Problem()

    # Add variables for each attribute value representing the house position
    for name in Names:
        problem.addVariable(var_name("Name", name), houses)
    for style in HouseStyles:
        problem.addVariable(var_name("HouseStyle", style), houses)
    for height in Heights:
        problem.addVariable(var_name("Height", height), houses)
    for edu in Educations:
        problem.addVariable(var_name("Education", edu), houses)

    # AllDifferent constraints within each category
    problem.addConstraint(AllDifferentConstraint(), [var_name("Name", n) for n in Names])
    problem.addConstraint(AllDifferentConstraint(), [var_name("HouseStyle", s) for s in HouseStyles])
    problem.addConstraint(AllDifferentConstraint(), [var_name("Height", h) for h in Heights])
    problem.addConstraint(AllDifferentConstraint(), [var_name("Education", e) for e in Educations])

    # Clue 1: The person who is short is directly left of Eric.
    problem.addConstraint(
        lambda short_pos, eric_pos: short_pos + 1 == eric_pos,
        (var_name("Height", "short"), var_name("Name", "Eric"))
    )

    # Clue 2: The person residing in a Victorian house is in the first house.
    problem.addConstraint(
        lambda victorian_pos: victorian_pos == 1,
        (var_name("HouseStyle", "victorian"),)
    )

    # Clue 3: The person who is short is the person with an associate's degree.
    problem.addConstraint(
        lambda short_pos, assoc_pos: short_pos == assoc_pos,
        (var_name("Height", "short"), var_name("Education", "associate"))
    )

    solutions = problem.getSolutions()
    if not solutions:
        output = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "Height", "Education"],
                "rows": []
            }
        }
        print(json.dumps(output))
        return

    sol = solutions[0]

    # Build rows ordered by house number
    rows = []
    for house in houses:
        # Find the value in each category that matches this house
        name = next(n for n in Names if sol[var_name("Name", n)] == house)
        style = next(s for s in HouseStyles if sol[var_name("HouseStyle", s)] == house)
        height = next(h for h in Heights if sol[var_name("Height", h)] == house)
        education = next(e for e in Educations if sol[var_name("Education", e)] == house)

        rows.append([str(house), name, style, height, education])

    output = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "Height", "Education"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()