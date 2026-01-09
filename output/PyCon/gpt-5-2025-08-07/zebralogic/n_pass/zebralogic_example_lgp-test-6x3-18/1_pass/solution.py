import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    houses = range(1, 7)

    names = ["Arnold", "Eric", "Bob", "Alice", "Carol", "Peter"]
    mothers = ["Sarah", "Holly", "Janelle", "Aniya", "Penny", "Kailyn"]
    pets = ["hamster", "dog", "bird", "cat", "fish", "rabbit"]

    prob = Problem()

    # Create variables for each category
    name_vars = [f"Name-{n}" for n in names]
    mother_vars = [f"Mother-{m}" for m in mothers]
    pet_vars = [f"Pet-{p}" for p in pets]

    for var in name_vars + mother_vars + pet_vars:
        prob.addVariable(var, houses)

    # All different within each category
    prob.addConstraint(AllDifferentConstraint(), name_vars)
    prob.addConstraint(AllDifferentConstraint(), mother_vars)
    prob.addConstraint(AllDifferentConstraint(), pet_vars)

    # Clue 1: Bob is not in the second house.
    prob.addConstraint(lambda b: b != 2, [f"Name-Bob"])

    # Clue 2: Two houses between the cat and the rabbit (difference of 3)
    prob.addConstraint(lambda c, r: abs(c - r) == 3, [f"Pet-cat", f"Pet-rabbit"])

    # Clue 3: cat directly left of Holly (mother)
    prob.addConstraint(lambda c, h: c == h - 1, [f"Pet-cat", f"Mother-Holly"])

    # Clue 4: hamster directly left of rabbit
    prob.addConstraint(lambda h, r: h == r - 1, [f"Pet-hamster", f"Pet-rabbit"])

    # Clue 5: rabbit is Eric
    prob.addConstraint(lambda r, e: r == e, [f"Pet-rabbit", f"Name-Eric"])

    # Clue 6: one house between dog and cat (difference of 2)
    prob.addConstraint(lambda d, c: abs(d - c) == 2, [f"Pet-dog", f"Pet-cat"])

    # Clue 7: cat is Janelle (mother)
    prob.addConstraint(lambda c, j: c == j, [f"Pet-cat", f"Mother-Janelle"])

    # Clue 8: Alice directly left of Carol
    prob.addConstraint(lambda a, c: a == c - 1, [f"Name-Alice", f"Name-Carol"])

    # Clue 9: Carol is Aniya (mother)
    prob.addConstraint(lambda c, a: c == a, [f"Name-Carol", f"Mother-Aniya"])

    # Clue 10: Arnold is the cat
    prob.addConstraint(lambda a, c: a == c, [f"Name-Arnold", f"Pet-cat"])

    # Clue 11: Kailyn is the rabbit (mother)
    prob.addConstraint(lambda k, r: k == r, [f"Mother-Kailyn", f"Pet-rabbit"])

    # Clue 12: fish is Sarah (mother)
    prob.addConstraint(lambda f, s: f == s, [f"Pet-fish", f"Mother-Sarah"])

    solution = prob.getSolution()
    if solution is None:
        raise ValueError("No solution found for the given puzzle.")

    # Invert mappings to find attributes per house
    house_to_name = {}
    for n in names:
        house_to_name[solution[f"Name-{n}"]] = n

    house_to_mother = {}
    for m in mothers:
        house_to_mother[solution[f"Mother-{m}"]] = m

    house_to_pet = {}
    for p in pets:
        house_to_pet[solution[f"Pet-{p}"]] = p

    rows = []
    for h in range(1, 7):
        rows.append([
            str(h),
            house_to_name[h],
            house_to_mother[h],
            house_to_pet[h]
        ])

    output = {
        "solution": {
            "header": ["House", "Name", "Mother", "Pet"],
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result))