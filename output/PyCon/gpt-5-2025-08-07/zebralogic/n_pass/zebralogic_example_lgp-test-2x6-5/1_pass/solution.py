import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Domains
    houses = [1, 2]
    names = ["Arnold", "Eric"]
    occupations = ["engineer", "doctor"]
    birthdays = ["april", "sept"]
    house_styles = ["victorian", "colonial"]
    heights = ["very short", "short"]
    cigars = ["pall mall", "prince"]

    # Helper to create variable identifiers
    def var(category, value):
        return (category, value)

    problem = Problem()

    # Add variables with domains
    for n in names:
        problem.addVariable(var("Name", n), houses)
    for o in occupations:
        problem.addVariable(var("Occupation", o), houses)
    for b in birthdays:
        problem.addVariable(var("Birthday", b), houses)
    for s in house_styles:
        problem.addVariable(var("HouseStyle", s), houses)
    for h in heights:
        problem.addVariable(var("Height", h), houses)
    for c in cigars:
        problem.addVariable(var("Cigar", c), houses)

    # All-different constraints within each category
    problem.addConstraint(AllDifferentConstraint(), [var("Name", n) for n in names])
    problem.addConstraint(AllDifferentConstraint(), [var("Occupation", o) for o in occupations])
    problem.addConstraint(AllDifferentConstraint(), [var("Birthday", b) for b in birthdays])
    problem.addConstraint(AllDifferentConstraint(), [var("HouseStyle", s) for s in house_styles])
    problem.addConstraint(AllDifferentConstraint(), [var("Height", h) for h in heights])
    problem.addConstraint(AllDifferentConstraint(), [var("Cigar", c) for c in cigars])

    # Clues:
    # 1. The person who is an engineer is in the first house.
    problem.addConstraint(lambda e: e == 1, [var("Occupation", "engineer")])

    # 2. The person whose birthday is in April and the person who is a doctor are next to each other.
    problem.addConstraint(lambda a, d: abs(a - d) == 1, [var("Birthday", "april"), var("Occupation", "doctor")])

    # 3. The person living in a colonial-style house is the person who is an engineer.
    problem.addConstraint(lambda c, e: c == e, [var("HouseStyle", "colonial"), var("Occupation", "engineer")])

    # 4. The person who is very short is the person who is an engineer.
    problem.addConstraint(lambda vs, e: vs == e, [var("Height", "very short"), var("Occupation", "engineer")])

    # 5. The person who is short is the person partial to Pall Mall.
    problem.addConstraint(lambda sh, pm: sh == pm, [var("Height", "short"), var("Cigar", "pall mall")])

    # 6. The person who is an engineer is Eric.
    problem.addConstraint(lambda e_occ, eric: e_occ == eric, [var("Occupation", "engineer"), var("Name", "Eric")])

    # Solve
    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No solution found")

    sol = solutions[0]

    # Build house-wise mapping
    def find_value_for_house(category, values, house_num):
        for v in values:
            if sol[var(category, v)] == house_num:
                return v
        return None

    rows = []
    for house in sorted(houses):
        name = find_value_for_house("Name", names, house)
        occupation = find_value_for_house("Occupation", occupations, house)
        birthday = find_value_for_house("Birthday", birthdays, house)
        style = find_value_for_house("HouseStyle", house_styles, house)
        height = find_value_for_house("Height", heights, house)
        cigar = find_value_for_house("Cigar", cigars, house)

        rows.append([
            str(house),
            name,
            occupation,
            birthday,
            style,
            height,
            cigar
        ])

    result = {
        "solution": {
            "header": ["House", "Name", "Occupation", "Birthday", "HouseStyle", "Height", "Cigar"],
            "rows": rows
        }
    }

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()