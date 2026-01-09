import json
from constraint import Problem, AllDifferentConstraint

def main():
    houses = [1, 2, 3, 4]

    categories = {
        "Name": ["Arnold", "Alice", "Eric", "Peter"],
        "Hobby": ["cooking", "painting", "photography", "gardening"],
        "Birthday": ["april", "jan", "sept", "feb"],
        "Education": ["master", "bachelor", "associate", "high school"],
        "Smoothie": ["cherry", "watermelon", "desert", "dragonfruit"],
    }

    # Initialize problem
    problem = Problem()

    # Add variables: each attribute value maps to a house number 1..4
    for cat, values in categories.items():
        for val in values:
            problem.addVariable((cat, val), houses)
        # All values in a category must be in different houses
        problem.addConstraint(AllDifferentConstraint(), [(cat, v) for v in values])

    # Helper to add equality constraints
    def eq(var1, var2):
        problem.addConstraint(lambda a, b: a == b, [var1, var2])

    # Helper to add adjacency constraints (difference == 1)
    def adjacent(var1, var2):
        problem.addConstraint(lambda a, b: abs(a - b) == 1, [var1, var2])

    # Helper to add spaced-by-one constraints (difference == 2)
    def spaced_by_one(var1, var2):
        problem.addConstraint(lambda a, b: abs(a - b) == 2, [var1, var2])

    # Clues:
    # 1. Desert smoothie lover == January birthday
    eq(("Smoothie", "desert"), ("Birthday", "jan"))

    # 2. Eric == bachelor's degree
    eq(("Name", "Eric"), ("Education", "bachelor"))

    # 3. January birthday == bachelor's degree
    eq(("Birthday", "jan"), ("Education", "bachelor"))

    # 4. High school diploma is in the third house
    problem.addConstraint(lambda x: x == 3, [("Education", "high school")])

    # 5. Watermelon smoothie lover is not in the third house
    problem.addConstraint(lambda x: x != 3, [("Smoothie", "watermelon")])

    # 6. Associate's degree == Arnold
    eq(("Education", "associate"), ("Name", "Arnold"))

    # 7. Master's degree == paints as a hobby
    eq(("Education", "master"), ("Hobby", "painting"))

    # 8. One house between Dragonfruit and September
    spaced_by_one(("Smoothie", "dragonfruit"), ("Birthday", "sept"))

    # 9. High school diploma == September birthday
    eq(("Education", "high school"), ("Birthday", "sept"))

    # 10. Loves cooking == Alice
    eq(("Hobby", "cooking"), ("Name", "Alice"))

    # 11. April and gardening are next to each other
    adjacent(("Birthday", "april"), ("Hobby", "gardening"))

    # 12. Paints as a hobby == February birthday
    eq(("Hobby", "painting"), ("Birthday", "feb"))

    # Solve
    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No solution found for the puzzle.")

    sol = solutions[0]

    # Build house-wise mapping
    by_house = {h: {"Name": None, "Hobby": None, "Birthday": None, "Education": None, "Smoothie": None} for h in houses}

    for cat, values in categories.items():
        for val in values:
            h = sol[(cat, val)]
            by_house[h][cat] = val

    # Prepare output JSON
    output = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Birthday", "Education", "Smoothie"],
            "rows": []
        }
    }

    for h in houses:
        row = [
            str(h),
            by_house[h]["Name"],
            by_house[h]["Hobby"],
            by_house[h]["Birthday"],
            by_house[h]["Education"],
            by_house[h]["Smoothie"],
        ]
        output["solution"]["rows"].append(row)

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()