import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define categories and their possible values
    categories = {
        "Name": ["Eric", "Arnold", "Peter"],
        "Vacation": ["mountain", "city", "beach"],
        "Height": ["very short", "average", "short"],
        "Flower": ["carnations", "daffodils", "lilies"],
        "HairColor": ["brown", "black", "blonde"],
        "Education": ["associate", "bachelor", "high school"],
    }

    def varname(cat, val):
        return f"{cat}_{val.replace(' ', '_')}"

    # Initialize problem
    problem = Problem()

    # Add variables: each attribute value maps to a house number (1..3)
    for cat, values in categories.items():
        for val in values:
            problem.addVariable(varname(cat, val), [1, 2, 3])

    # AllDifferent constraints within each category (each value must be in a unique house)
    for cat, values in categories.items():
        problem.addConstraint(AllDifferentConstraint(), [varname(cat, v) for v in values])

    # Clues as constraints
    # 1. Peter is the person who has an average height.
    problem.addConstraint(lambda a, b: a == b, (varname("Name", "Peter"), varname("Height", "average")))

    # 2. The person who loves a bouquet of daffodils is Arnold.
    problem.addConstraint(lambda a, b: a == b, (varname("Flower", "daffodils"), varname("Name", "Arnold")))

    # 3. The person who is very short is not in the second house.
    problem.addConstraint(lambda h: h != 2, (varname("Height", "very short"),))

    # 4. The person who loves beach vacations is in the first house.
    problem.addConstraint(lambda h: h == 1, (varname("Vacation", "beach"),))

    # 5. The person with a high school diploma is in the third house.
    problem.addConstraint(lambda h: h == 3, (varname("Education", "high school"),))

    # 6. The person who is short is somewhere to the right of the person who is very short.
    problem.addConstraint(lambda s, vs: s > vs, (varname("Height", "short"), varname("Height", "very short")))

    # 7. The person who loves the boquet of lilies is Eric.
    problem.addConstraint(lambda a, b: a == b, (varname("Flower", "lilies"), varname("Name", "Eric")))

    # 8. The person who loves the boquet of lilies is the person with a bachelor's degree.
    problem.addConstraint(lambda a, b: a == b, (varname("Flower", "lilies"), varname("Education", "bachelor")))

    # 9. The person who prefers city breaks is somewhere to the right of Peter.
    problem.addConstraint(lambda city, peter: city > peter, (varname("Vacation", "city"), varname("Name", "Peter")))

    # 10. The person who has blonde hair is in the third house.
    problem.addConstraint(lambda h: h == 3, (varname("HairColor", "blonde"),))

    # 11. The person who loves beach vacations is the person who has brown hair.
    problem.addConstraint(lambda a, b: a == b, (varname("Vacation", "beach"), varname("HairColor", "brown")))

    # Solve
    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No solution found for the given puzzle.")

    sol = solutions[0]

    # Helper to find the value for a category at a specific house
    def value_at_house(category, house):
        for v in categories[category]:
            if sol[varname(category, v)] == house:
                return v
        return None

    # Build rows per house
    rows = []
    for house in [1, 2, 3]:
        row = [
            str(house),
            value_at_house("Name", house),
            value_at_house("Vacation", house),
            value_at_house("Height", house),
            value_at_house("Flower", house),
            value_at_house("HairColor", house),
            value_at_house("Education", house),
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": ["House", "Name", "Vacation", "Height", "Flower", "HairColor", "Education"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()