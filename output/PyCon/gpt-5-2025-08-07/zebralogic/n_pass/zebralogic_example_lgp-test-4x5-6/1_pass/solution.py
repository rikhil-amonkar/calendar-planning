import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Domains
    houses = [1, 2, 3, 4]
    Names = ["Peter", "Eric", "Alice", "Arnold"]
    Education = ["bachelor", "high school", "associate", "master"]
    Music = ["jazz", "rock", "pop", "classical"]
    Colors = ["green", "red", "yellow", "white"]
    Flowers = ["lilies", "carnations", "daffodils", "roses"]

    # Setup problem
    problem = Problem()

    # Add variables for each attribute item with domain as house positions
    for var in Names + Education + Music + Colors + Flowers:
        problem.addVariable(var, houses)

    # Uniqueness within each category
    problem.addConstraint(AllDifferentConstraint(), Names)
    problem.addConstraint(AllDifferentConstraint(), Education)
    problem.addConstraint(AllDifferentConstraint(), Music)
    problem.addConstraint(AllDifferentConstraint(), Colors)
    problem.addConstraint(AllDifferentConstraint(), Flowers)

    # Clues:
    # 1. bachelor's degree <-> daffodils
    problem.addConstraint(lambda b, d: b == d, ("bachelor", "daffodils"))

    # 2. carnations not in first
    problem.addConstraint(lambda c: c != 1, ("carnations",))

    # 3. master's degree is Alice
    problem.addConstraint(lambda m, a: m == a, ("master", "Alice"))

    # 4. master directly left of classical music
    problem.addConstraint(lambda m, c: m == c - 1, ("master", "classical"))

    # 5. Eric not in second
    problem.addConstraint(lambda e: e != 2, ("Eric",))

    # 6. Arnold not in third
    problem.addConstraint(lambda a: a != 3, ("Arnold",))

    # 7. yellow directly left of roses
    problem.addConstraint(lambda y, r: y == r - 1, ("yellow", "roses"))

    # 8. pop music in second
    problem.addConstraint(lambda p: p == 2, ("pop",))

    # 9. associate not in fourth
    problem.addConstraint(lambda a: a != 4, ("associate",))

    # 10. carnations not in fourth
    problem.addConstraint(lambda c: c != 4, ("carnations",))

    # 11. red directly left of white
    problem.addConstraint(lambda r, w: r == w - 1, ("red", "white"))

    # 12. red is rock
    problem.addConstraint(lambda r, rock: r == rock, ("red", "rock"))

    # 13. Arnold is yellow
    problem.addConstraint(lambda ar, y: ar == y, ("Arnold", "yellow"))

    # 14. daffodils is yellow
    problem.addConstraint(lambda d, y: d == y, ("daffodils", "yellow"))

    # Solve
    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No solution found for the puzzle.")

    sol = solutions[0]

    # Helper to find attribute for a given house
    def find_for_house(h, items):
        for item in items:
            if sol[item] == h:
                return item
        return None

    header = ["House", "Name", "Education", "MusicGenre", "Color", "Flower"]
    rows = []
    for h in houses:
        rows.append([
            str(h),
            find_for_house(h, Names),
            find_for_house(h, Education),
            find_for_house(h, Music),
            find_for_house(h, Colors),
            find_for_house(h, Flowers),
        ])

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()