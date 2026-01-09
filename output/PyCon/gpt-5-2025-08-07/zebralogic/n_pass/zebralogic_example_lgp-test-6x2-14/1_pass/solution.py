import json
from constraint import Problem, AllDifferentConstraint

def main():
    houses = range(1, 7)

    names = ["Carol", "Peter", "Eric", "Arnold", "Alice", "Bob"]
    cigars = ["blends", "yellow monster", "pall mall", "blue master", "dunhill", "prince"]

    # Map cigars to solver-friendly variable names
    cigar_vars = {c: f"cigar_{c.replace(' ', '_')}" for c in cigars}

    problem = Problem()

    # Add variables: each name and each cigar has a unique house 1..6
    problem.addVariables(names, houses)
    problem.addVariables(list(cigar_vars.values()), houses)

    # All different constraints within each category
    problem.addConstraint(AllDifferentConstraint(), names)
    problem.addConstraint(AllDifferentConstraint(), list(cigar_vars.values()))

    # Clues:
    # 1. Arnold is somewhere to the left of the person who smokes many unique blends.
    problem.addConstraint(lambda arn, bl: arn < bl, ("Arnold", cigar_vars["blends"]))

    # 2. The person who smokes Blue Master is in the fifth house.
    problem.addConstraint(lambda x: x == 5, (cigar_vars["blue master"],))

    # 3. Arnold is somewhere to the left of the Prince smoker.
    problem.addConstraint(lambda arn, pr: arn < pr, ("Arnold", cigar_vars["prince"]))

    # 4. There is one house between Yellow Monster and blends.
    problem.addConstraint(lambda ym, bl: abs(ym - bl) == 2,
                          (cigar_vars["yellow monster"], cigar_vars["blends"]))

    # 5. The person partial to Pall Mall is in the third house.
    problem.addConstraint(lambda x: x == 3, (cigar_vars["pall mall"],))

    # 6. Eric is in the sixth house.
    problem.addConstraint(lambda x: x == 6, ("Eric",))

    # 7. Carol and Eric are next to each other.
    problem.addConstraint(lambda carol, eric: abs(carol - eric) == 1, ("Carol", "Eric"))

    # 8. Peter is in the first house.
    problem.addConstraint(lambda x: x == 1, ("Peter",))

    # 9. Bob is in the third house.
    problem.addConstraint(lambda x: x == 3, ("Bob",))

    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No solution found for the given puzzle constraints.")
    # Assuming unique solution; take the first
    sol = solutions[0]

    # Build output rows ordered by house 1..6
    rows = []
    for h in range(1, 7):
        # Find the name at house h
        name_at_h = next(n for n in names if sol[n] == h)
        # Find the cigar at house h
        cigar_at_h = next(c for c in cigars if sol[cigar_vars[c]] == h)
        rows.append([str(h), name_at_h, cigar_at_h])

    output = {
        "solution": {
            "header": ["House", "Name", "Cigar"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()