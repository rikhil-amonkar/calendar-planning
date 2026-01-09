import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()

    houses = range(1, 6)

    Names = ["Alice", "Peter", "Bob", "Eric", "Arnold"]
    Heights = ["very short", "short", "tall", "average", "very tall"]
    Mothers = ["Janelle", "Kailyn", "Penny", "Holly", "Aniya"]
    HairColors = ["blonde", "black", "gray", "red", "brown"]

    # Add variables with domains 1..5 (house positions)
    for n in Names:
        problem.addVariable(n, houses)
    for h in Heights:
        problem.addVariable(h, houses)
    for m in Mothers:
        problem.addVariable(m, houses)
    for c in HairColors:
        problem.addVariable(c, houses)

    # All different constraints within each category
    problem.addConstraint(AllDifferentConstraint(), Names)
    problem.addConstraint(AllDifferentConstraint(), Heights)
    problem.addConstraint(AllDifferentConstraint(), Mothers)
    problem.addConstraint(AllDifferentConstraint(), HairColors)

    # Clues as constraints:

    # 1. The person who is tall is The person whose mother's name is Holly.
    problem.addConstraint(lambda t, h: t == h, ("tall", "Holly"))

    # 2. Two houses between average and short -> distance 3
    problem.addConstraint(lambda a, s: abs(a - s) == 3, ("average", "short"))

    # 3. Gray hair is directly left of Janelle
    problem.addConstraint(lambda g, j: g == j - 1, ("gray", "Janelle"))

    # 4. Black hair is not in the fourth house
    problem.addConstraint(lambda b: b != 4, ("black",))

    # 5. Eric has black hair
    problem.addConstraint(lambda eric, black: eric == black, ("Eric", "black"))

    # 6. Very short is Penny
    problem.addConstraint(lambda vs, p: vs == p, ("very short", "Penny"))

    # 7. Eric and gray hair are next to each other
    problem.addConstraint(lambda eric, gray: abs(eric - gray) == 1, ("Eric", "gray"))

    # 8. Bob is in the fifth house
    problem.addConstraint(lambda bob: bob == 5, ("Bob",))

    # 9. Red hair is Peter
    problem.addConstraint(lambda red, peter: red == peter, ("red", "Peter"))

    # 10. Kailyn is directly left of the short person
    problem.addConstraint(lambda k, s: k == s - 1, ("Kailyn", "short"))

    # 11. Arnold has brown hair
    problem.addConstraint(lambda arnold, brown: arnold == brown, ("Arnold", "brown"))

    # 12. Brown hair is left of Janelle
    problem.addConstraint(lambda brown, j: brown < j, ("brown", "Janelle"))

    # 13. Aniya and very short are next to each other
    problem.addConstraint(lambda aniya, vs: abs(aniya - vs) == 1, ("Aniya", "very short"))

    # 14. Kailyn is in the third house
    problem.addConstraint(lambda k: k == 3, ("Kailyn",))

    solutions = problem.getSolutions()

    if not solutions:
        raise ValueError("No solution found for the given puzzle constraints.")

    # Assume unique solution or take the first
    sol = solutions[0]

    # Invert mappings to get attribute per house
    name_by_pos = {sol[name]: name for name in Names}
    height_by_pos = {sol[h]: h for h in Heights}
    mother_by_pos = {sol[m]: m for m in Mothers}
    hair_by_pos = {sol[c]: c for c in HairColors}

    header = ["House", "Name", "Height", "Mother", "HairColor"]
    rows = []
    for i in range(1, 6):
        row = [str(i), name_by_pos[i], height_by_pos[i], mother_by_pos[i], hair_by_pos[i]]
        rows.append(row)

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve_puzzle()