import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    houses = [1, 2, 3]

    categories = {
        "Name": ["Eric", "Peter", "Arnold"],
        "Cigar": ["blue master", "prince", "pall mall"],
        "Hobby": ["photography", "gardening", "cooking"],
        "Education": ["high school", "associate", "bachelor"],
        "Drink": ["tea", "milk", "water"],
    }

    problem = Problem()

    # Create variables for each attribute value indicating the house position (1..3)
    for category, values in categories.items():
        for val in values:
            problem.addVariable((category, val), houses)

    # AllDifferent constraints within each category
    for category, values in categories.items():
        problem.addConstraint(
            AllDifferentConstraint(),
            [(category, val) for val in values]
        )

    # Clue 1: The person partial to Pall Mall is Peter.
    problem.addConstraint(
        lambda pp, np: pp == np,
        (("Cigar", "pall mall"), ("Name", "Peter"))
    )

    # Clue 2: The person who likes milk is directly left of the person with a high school diploma.
    problem.addConstraint(
        lambda milk, hs: milk == hs - 1,
        (("Drink", "milk"), ("Education", "high school"))
    )

    # Clue 3: Eric is the tea drinker.
    problem.addConstraint(
        lambda ne, dt: ne == dt,
        (("Name", "Eric"), ("Drink", "tea"))
    )

    # Clue 4: Arnold and the Prince smoker are next to each other.
    problem.addConstraint(
        lambda na, cp: abs(na - cp) == 1,
        (("Name", "Arnold"), ("Cigar", "prince"))
    )

    # Clue 5: The person who enjoys gardening is somewhere to the left of the Prince smoker.
    problem.addConstraint(
        lambda hg, cp: hg < cp,
        (("Hobby", "gardening"), ("Cigar", "prince"))
    )

    # Clue 6: The person who likes milk is the person with an associate's degree.
    problem.addConstraint(
        lambda milk, assoc: milk == assoc,
        (("Drink", "milk"), ("Education", "associate"))
    )

    # Clue 7: The person with a bachelor's degree is directly left of the photography enthusiast.
    problem.addConstraint(
        lambda bach, photo: bach == photo - 1,
        (("Education", "bachelor"), ("Hobby", "photography"))
    )

    solutions = problem.getSolutions()

    if not solutions:
        raise ValueError("No solution found for the given puzzle.")

    # Assuming unique solution; take the first
    sol = solutions[0]

    # Build rows for each house in order 1..3
    rows = []
    for h in houses:
        name = next(v for v in categories["Name"] if sol[("Name", v)] == h)
        cigar = next(v for v in categories["Cigar"] if sol[("Cigar", v)] == h)
        hobby = next(v for v in categories["Hobby"] if sol[("Hobby", v)] == h)
        education = next(v for v in categories["Education"] if sol[("Education", v)] == h)
        drink = next(v for v in categories["Drink"] if sol[("Drink", v)] == h)
        rows.append([str(h), name, cigar, hobby, education, drink])

    output = {
        "solution": {
            "header": ["House", "Name", "Cigar", "Hobby", "Education", "Drink"],
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False, indent=2))