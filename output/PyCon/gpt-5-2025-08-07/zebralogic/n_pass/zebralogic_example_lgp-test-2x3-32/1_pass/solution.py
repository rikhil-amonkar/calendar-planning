import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define categories and domains
    houses = [1, 2]
    names = ["Eric", "Arnold"]
    birthdays = ["sept", "april"]
    colors = ["yellow", "red"]

    # Initialize problem
    problem = Problem()

    # Variables: each attribute value maps to a house number
    problem.addVariables(names, houses)
    problem.addVariables(birthdays, houses)
    problem.addVariables(colors, houses)

    # Uniqueness constraints per category
    problem.addConstraint(AllDifferentConstraint(), names)
    problem.addConstraint(AllDifferentConstraint(), birthdays)
    problem.addConstraint(AllDifferentConstraint(), colors)

    # Clues:
    # 1. Eric is the person who loves yellow.
    problem.addConstraint(lambda eric_house, yellow_house: eric_house == yellow_house, ("Eric", "yellow"))

    # 2. The person whose birthday is in April is in the first house.
    problem.addConstraint(lambda h: h == 1, ("april",))

    # 3. The person who loves yellow is not in the first house.
    problem.addConstraint(lambda h: h != 1, ("yellow",))

    # Compute solution
    solution = problem.getSolution()
    if not solution:
        raise ValueError("No solution found for the given puzzle.")

    # Build rows per house in order
    rows = []
    for h in sorted(houses):
        name = next(n for n in names if solution[n] == h)
        birthday = next(b for b in birthdays if solution[b] == h)
        color = next(c for c in colors if solution[c] == h)
        rows.append([str(h), name, birthday, color])

    output = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Color"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()