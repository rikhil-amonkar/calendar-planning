import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    houses = [1, 2, 3, 4]

    # Categories and items
    Names = ["Peter", "Arnold", "Eric", "Alice"]
    Flowers = ["daffodils", "carnations", "roses", "lilies"]
    Heights = ["very short", "short", "tall", "average"]
    Mothers = ["Janelle", "Kailyn", "Holly", "Aniya"]
    Occupations = ["engineer", "doctor", "teacher", "artist"]
    Sports = ["swimming", "basketball", "tennis", "soccer"]

    problem = Problem()

    # Add variables for each item with domain as house numbers
    for item in Names + Flowers + Heights + Mothers + Occupations + Sports:
        problem.addVariable(item, houses)

    # AllDifferent within each category
    problem.addConstraint(AllDifferentConstraint(), Names)
    problem.addConstraint(AllDifferentConstraint(), Flowers)
    problem.addConstraint(AllDifferentConstraint(), Heights)
    problem.addConstraint(AllDifferentConstraint(), Mothers)
    problem.addConstraint(AllDifferentConstraint(), Occupations)
    problem.addConstraint(AllDifferentConstraint(), Sports)

    # Clues:
    # 1. The person who loves swimming is the person who loves the rose bouquet.
    problem.addConstraint(lambda s, r: s == r, ("swimming", "roses"))

    # 2. The person who loves the rose bouquet is Eric.
    problem.addConstraint(lambda r, e: r == e, ("roses", "Eric"))

    # 3. Arnold is the person who is tall.
    problem.addConstraint(lambda a, t: a == t, ("Arnold", "tall"))

    # 4. The person who loves a bouquet of daffodils is somewhere to the right of the person who is an engineer.
    problem.addConstraint(lambda d, e: d > e, ("daffodils", "engineer"))

    # 5. The person who loves soccer is the person who is short.
    problem.addConstraint(lambda s, sh: s == sh, ("soccer", "short"))

    # 6. The person who is a teacher is in the first house.
    problem.addConstraint(lambda t: t == 1, ("teacher",))

    # 7. The person whose mother's name is Janelle is the person who loves a carnations arrangement.
    problem.addConstraint(lambda j, c: j == c, ("Janelle", "carnations"))

    # 8. The person who loves basketball is the person who has an average height.
    problem.addConstraint(lambda b, a: b == a, ("basketball", "average"))

    # 9. Arnold is not in the third house.
    problem.addConstraint(lambda a: a != 3, ("Arnold",))

    # 10. The person whose mother's name is Holly is somewhere to the right of the person who has an average height.
    problem.addConstraint(lambda h, a: h > a, ("Holly", "average"))

    # 11. Peter is the person who is a doctor.
    problem.addConstraint(lambda p, d: p == d, ("Peter", "doctor"))

    # 12. The person whose mother's name is Aniya is Alice.
    problem.addConstraint(lambda an, al: an == al, ("Aniya", "Alice"))

    # 13. Arnold is the person who loves the boquet of lilies.
    problem.addConstraint(lambda ar, li: ar == li, ("Arnold", "lilies"))

    solutions = problem.getSolutions()
    if not solutions:
        raise ValueError("No solution found for the puzzle.")

    sol = solutions[0]

    # Build rows per house
    rows = []
    for h in houses:
        name = next(n for n in Names if sol[n] == h)
        flower = next(f for f in Flowers if sol[f] == h)
        height = next(ht for ht in Heights if sol[ht] == h)
        mother = next(m for m in Mothers if sol[m] == h)
        occupation = next(o for o in Occupations if sol[o] == h)
        sport = next(s for s in Sports if sol[s] == h)
        rows.append([str(h), name, flower, height, mother, occupation, sport])

    output = {
        "solution": {
            "header": ["House", "Name", "Flower", "Height", "Mother", "Occupation", "FavoriteSport"],
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))