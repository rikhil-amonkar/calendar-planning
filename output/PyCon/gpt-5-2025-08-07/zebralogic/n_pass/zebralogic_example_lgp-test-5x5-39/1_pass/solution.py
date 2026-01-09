import json
from constraint import Problem, AllDifferentConstraint

def main():
    houses = range(1, 6)

    names = ["Alice", "Eric", "Bob", "Peter", "Arnold"]
    birthdays = ["mar", "april", "sept", "feb", "jan"]
    mothers = ["Holly", "Janelle", "Kailyn", "Penny", "Aniya"]
    occupations = ["engineer", "doctor", "lawyer", "artist", "teacher"]
    hair_colors = ["red", "blonde", "black", "gray", "brown"]

    problem = Problem()

    # Add variables for each attribute value representing the house number (1..5)
    for val in names + birthdays + mothers + occupations + hair_colors:
        problem.addVariable(val, houses)

    # AllDifferent constraints per category
    problem.addConstraint(AllDifferentConstraint(), names)
    problem.addConstraint(AllDifferentConstraint(), birthdays)
    problem.addConstraint(AllDifferentConstraint(), mothers)
    problem.addConstraint(AllDifferentConstraint(), occupations)
    problem.addConstraint(AllDifferentConstraint(), hair_colors)

    # Clues
    # 1. March is in the fifth house.
    problem.addConstraint(lambda m: m == 5, ("mar",))
    # 2. February is in the first house.
    problem.addConstraint(lambda f: f == 1, ("feb",))
    # 3. The doctor is Eric.
    problem.addConstraint(lambda d, e: d == e, ("doctor", "Eric"))
    # 4. Janelle is in the third house.
    problem.addConstraint(lambda j: j == 3, ("Janelle",))
    # 5. The artist has brown hair.
    problem.addConstraint(lambda a, b: a == b, ("artist", "brown"))
    # 6. The artist is in the fourth house.
    problem.addConstraint(lambda a: a == 4, ("artist",))
    # 7. Penny is somewhere to the left of black hair.
    problem.addConstraint(lambda p, b: p < b, ("Penny", "black"))
    # 8. Peter has black hair.
    problem.addConstraint(lambda p, b: p == b, ("Peter", "black"))
    # 9. Gray hair is the teacher.
    problem.addConstraint(lambda g, t: g == t, ("gray", "teacher"))
    # 10. Alice's mother is Kailyn.
    problem.addConstraint(lambda a, k: a == k, ("Alice", "Kailyn"))
    # 11. Arnold is somewhere to the right of September.
    problem.addConstraint(lambda ar, s: ar > s, ("Arnold", "sept"))
    # 12. Brown hair's birthday is in January.
    problem.addConstraint(lambda br, j: br == j, ("brown", "jan"))
    # 13. Arnold has blonde hair.
    problem.addConstraint(lambda ar, bl: ar == bl, ("Arnold", "blonde"))
    # 14. Holly is the mother of the person with black hair.
    problem.addConstraint(lambda h, b: h == b, ("Holly", "black"))
    # 15. Peter is a lawyer.
    problem.addConstraint(lambda p, l: p == l, ("Peter", "lawyer"))
    # 16. September is somewhere to the left of Kailyn.
    problem.addConstraint(lambda s, k: s < k, ("sept", "Kailyn"))
    # 17. Alice has gray hair.
    problem.addConstraint(lambda a, g: a == g, ("Alice", "gray"))

    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No solution found")

    sol = solutions[0]

    # Build output rows per house
    rows = []
    for house in sorted(houses):
        # Find values for each category at this house
        name = next(n for n in names if sol[n] == house)
        birthday = next(b for b in birthdays if sol[b] == house)
        mother = next(m for m in mothers if sol[m] == house)
        occupation = next(o for o in occupations if sol[o] == house)
        hair = next(h for h in hair_colors if sol[h] == house)
        rows.append([str(house), name, birthday, mother, occupation, hair])

    output = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Mother", "Occupation", "HairColor"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()