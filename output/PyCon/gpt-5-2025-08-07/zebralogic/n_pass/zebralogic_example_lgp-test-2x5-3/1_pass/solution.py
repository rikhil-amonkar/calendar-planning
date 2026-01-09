import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define houses and categories
    houses = [1, 2]
    categories = {
        "Name": ["Eric", "Arnold"],
        "Hobby": ["gardening", "photography"],
        "BookGenre": ["science fiction", "mystery"],
        "MusicGenre": ["rock", "pop"],
        "Birthday": ["april", "sept"],
    }

    # Initialize the problem
    problem = Problem()

    # Helper to create a variable key
    def var_key(category, value):
        return (category, value)

    # Add variables for each attribute value with domain of houses
    for category, values in categories.items():
        for value in values:
            problem.addVariable(var_key(category, value), houses)

    # Each category must be a bijection to houses (AllDifferent within category)
    for category, values in categories.items():
        problem.addConstraint(
            AllDifferentConstraint(),
            [var_key(category, v) for v in values]
        )

    # Clues:
    # 1. The person who loves mystery books is the person who loves rock music.
    problem.addConstraint(
        lambda bm, mr: bm == mr,
        (var_key("BookGenre", "mystery"), var_key("MusicGenre", "rock"))
    )

    # 2. Arnold is not in the first house.
    problem.addConstraint(
        lambda a: a != 1,
        (var_key("Name", "Arnold"),)
    )

    # 3. The person who loves mystery books is the person who enjoys gardening.
    problem.addConstraint(
        lambda bm, hg: bm == hg,
        (var_key("BookGenre", "mystery"), var_key("Hobby", "gardening"))
    )

    # 4. The person whose birthday is in April is Arnold.
    problem.addConstraint(
        lambda ap, ar: ap == ar,
        (var_key("Birthday", "april"), var_key("Name", "Arnold"))
    )

    # 5. The person who loves mystery books is in the first house.
    problem.addConstraint(
        lambda bm: bm == 1,
        (var_key("BookGenre", "mystery"),)
    )

    # Solve
    solutions = problem.getSolutions()
    if not solutions:
        # Should not happen for a valid puzzle; return empty structured JSON if no solution
        output = {
            "solution": {
                "header": ["House", "Name", "Hobby", "BookGenre", "MusicGenre", "Birthday"],
                "rows": []
            }
        }
        print(json.dumps(output, ensure_ascii=False))
        return

    sol = solutions[0]

    # Build the output rows in house order
    header = ["House", "Name", "Hobby", "BookGenre", "MusicGenre", "Birthday"]

    def value_in_house(category, house):
        for v in categories[category]:
            if sol[var_key(category, v)] == house:
                return v
        return None

    rows = []
    for h in houses:
        row = [
            str(h),
            value_in_house("Name", h),
            value_in_house("Hobby", h),
            value_in_house("BookGenre", h),
            value_in_house("MusicGenre", h),
            value_in_house("Birthday", h),
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()