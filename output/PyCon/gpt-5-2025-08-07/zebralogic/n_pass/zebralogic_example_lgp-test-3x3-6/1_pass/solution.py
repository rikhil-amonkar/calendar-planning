import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Domains
    houses = [1, 2, 3]
    names = ["Eric", "Arnold", "Peter"]
    genres = ["mystery", "science fiction", "romance"]
    vacations = ["mountain", "beach", "city"]

    # Initialize problem
    problem = Problem()

    # Create variables for each attribute mapping to a house number
    name_vars = [f"Name_{n}" for n in names]
    book_vars = [f"Book_{g}" for g in genres]
    vacation_vars = [f"Vacation_{v}" for v in vacations]

    problem.addVariables(name_vars, houses)
    problem.addVariables(book_vars, houses)
    problem.addVariables(vacation_vars, houses)

    # All-different constraints within each category
    problem.addConstraint(AllDifferentConstraint(), name_vars)
    problem.addConstraint(AllDifferentConstraint(), book_vars)
    problem.addConstraint(AllDifferentConstraint(), vacation_vars)

    # Helper to access variable names
    def N(name): return f"Name_{name}"
    def B(genre): return f"Book_{genre}"
    def V(vac): return f"Vacation_{vac}"

    # Clues:
    # 1. Eric is directly left of Arnold.
    problem.addConstraint(lambda e, a: e + 1 == a, (N("Eric"), N("Arnold")))

    # 2. Peter is somewhere to the right of the person who loves beach vacations.
    problem.addConstraint(lambda p, b: p > b, (N("Peter"), V("beach")))

    # 3. Peter is the person who prefers city breaks.
    problem.addConstraint(lambda p, c: p == c, (N("Peter"), V("city")))

    # 4. The person who loves mystery books is somewhere to the left of the person who loves beach vacations.
    problem.addConstraint(lambda m, b: m < b, (B("mystery"), V("beach")))

    # 5. The person who loves science fiction books is the person who loves beach vacations.
    problem.addConstraint(lambda s, b: s == b, (B("science fiction"), V("beach")))

    # Solve
    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No solution found for the given puzzle.")

    # Assuming unique solution; take the first
    sol = solutions[0]

    # Build rows in house order
    rows = []
    for house in sorted(houses):
        # Find which name/book/vacation is at this house
        name_at_house = next(n for n in names if sol[N(n)] == house)
        book_at_house = next(g for g in genres if sol[B(g)] == house)
        vacation_at_house = next(v for v in vacations if sol[V(v)] == house)

        rows.append([str(house), name_at_house, book_at_house, vacation_at_house])

    output = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Vacation"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()