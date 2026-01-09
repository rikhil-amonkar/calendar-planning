import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    houses = [1, 2]

    problem = Problem()

    # Variables per attribute value -> house number
    name_vars = {
        "Eric": "N_Eric",
        "Arnold": "N_Arnold",
    }
    book_vars = {
        "science fiction": "B_science fiction",
        "mystery": "B_mystery",
    }
    birthday_vars = {
        "april": "D_april",
        "sept": "D_sept",
    }
    animal_vars = {
        "horse": "A_horse",
        "cat": "A_cat",
    }

    # Add variables with domains
    for var in name_vars.values():
        problem.addVariable(var, houses)
    for var in book_vars.values():
        problem.addVariable(var, houses)
    for var in birthday_vars.values():
        problem.addVariable(var, houses)
    for var in animal_vars.values():
        problem.addVariable(var, houses)

    # All-different within each category
    problem.addConstraint(AllDifferentConstraint(), list(name_vars.values()))
    problem.addConstraint(AllDifferentConstraint(), list(book_vars.values()))
    problem.addConstraint(AllDifferentConstraint(), list(birthday_vars.values()))
    problem.addConstraint(AllDifferentConstraint(), list(animal_vars.values()))

    # Clues:
    # 1. Eric is in the first house.
    problem.addConstraint(lambda e: e == 1, (name_vars["Eric"],))

    # 2. Eric is the person whose birthday is in September.
    problem.addConstraint(lambda e, s: e == s, (name_vars["Eric"], birthday_vars["sept"]))

    # 3. The person who loves science fiction books is in the second house.
    problem.addConstraint(lambda sf: sf == 2, (book_vars["science fiction"],))

    # 4. The person who keeps horses is the person whose birthday is in September.
    problem.addConstraint(lambda h, s: h == s, (animal_vars["horse"], birthday_vars["sept"]))

    solutions = problem.getSolutions()
    if not solutions:
        raise ValueError("No solution found for the given puzzle constraints.")
    sol = solutions[0]

    # Build mappings from house -> value for each category
    name_by_house = {sol[name_vars["Eric"]]: "Eric", sol[name_vars["Arnold"]]: "Arnold"}
    book_by_house = {
        sol[book_vars["science fiction"]]: "science fiction",
        sol[book_vars["mystery"]]: "mystery",
    }
    birthday_by_house = {
        sol[birthday_vars["april"]]: "april",
        sol[birthday_vars["sept"]]: "sept",
    }
    animal_by_house = {
        sol[animal_vars["horse"]]: "horse",
        sol[animal_vars["cat"]]: "cat",
    }

    rows = []
    for h in sorted(houses):
        rows.append([
            str(h),
            name_by_house[h],
            book_by_house[h],
            birthday_by_house[h],
            animal_by_house[h],
        ])

    result = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Birthday", "Animal"],
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))