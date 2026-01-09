import json
from constraint import Problem, AllDifferentConstraint

def sanitize(value):
    return value.replace(" ", "_")

def var(category, value):
    return f"{category}_{sanitize(value)}"

def main():
    # Houses (left to right)
    houses = [1, 2]

    # Attributes
    names = ["Eric", "Arnold"]
    hobbies = ["gardening", "photography"]
    pets = ["cat", "dog"]
    heights = ["short", "very short"]

    # Initialize problem
    problem = Problem()

    # Add variables for each attribute value with domain = house positions
    for n in names:
        problem.addVariable(var("Name", n), houses)
    for h in hobbies:
        problem.addVariable(var("Hobby", h), houses)
    for p in pets:
        problem.addVariable(var("Pet", p), houses)
    for ht in heights:
        problem.addVariable(var("Height", ht), houses)

    # Uniqueness constraints within each category
    problem.addConstraint(AllDifferentConstraint(), [var("Name", n) for n in names])
    problem.addConstraint(AllDifferentConstraint(), [var("Hobby", h) for h in hobbies])
    problem.addConstraint(AllDifferentConstraint(), [var("Pet", p) for p in pets])
    problem.addConstraint(AllDifferentConstraint(), [var("Height", ht) for ht in heights])

    # Clue 1: The person who is very short is the photography enthusiast.
    problem.addConstraint(
        lambda hv, hp: hv == hp,
        (var("Height", "very short"), var("Hobby", "photography"))
    )

    # Clue 2: Eric is the person who is very short.
    problem.addConstraint(
        lambda ne, hv: ne == hv,
        (var("Name", "Eric"), var("Height", "very short"))
    )

    # Clue 3: The person who has a cat is somewhere to the right of the person who is very short.
    problem.addConstraint(
        lambda pc, hv: pc > hv,
        (var("Pet", "cat"), var("Height", "very short"))
    )

    # Solve
    solutions = problem.getSolutions()
    if not solutions:
        raise ValueError("No solution found for the given puzzle.")

    sol = solutions[0]

    # Build house-wise mapping
    house_to_name = {}
    house_to_hobby = {}
    house_to_pet = {}
    house_to_height = {}

    for h in houses:
        for n in names:
            if sol[var("Name", n)] == h:
                house_to_name[h] = n
        for hb in hobbies:
            if sol[var("Hobby", hb)] == h:
                house_to_hobby[h] = hb
        for p in pets:
            if sol[var("Pet", p)] == h:
                house_to_pet[h] = p
        for ht in heights:
            if sol[var("Height", ht)] == h:
                house_to_height[h] = ht

    # Prepare JSON output
    output = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Pet", "Height"],
            "rows": []
        }
    }

    for h in houses:
        row = [
            str(h),
            house_to_name[h],
            house_to_hobby[h],
            house_to_pet[h],
            house_to_height[h]
        ]
        output["solution"]["rows"].append(row)

    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()