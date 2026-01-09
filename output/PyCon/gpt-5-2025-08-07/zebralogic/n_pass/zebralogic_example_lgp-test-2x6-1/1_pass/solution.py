import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    houses = [1, 2]

    # Attributes
    Names = ["Arnold", "Eric"]
    FavoriteSports = ["basketball", "soccer"]
    HairColors = ["brown", "black"]
    Heights = ["very short", "short"]
    Smoothies = ["desert", "cherry"]
    Flowers = ["daffodils", "carnations"]

    problem = Problem()

    # Add variables: each attribute value corresponds to a house number
    for n in Names:
        problem.addVariable(("Name", n), houses)
    for s in FavoriteSports:
        problem.addVariable(("FavoriteSport", s), houses)
    for hc in HairColors:
        problem.addVariable(("HairColor", hc), houses)
    for h in Heights:
        problem.addVariable(("Height", h), houses)
    for sm in Smoothies:
        problem.addVariable(("Smoothie", sm), houses)
    for f in Flowers:
        problem.addVariable(("Flower", f), houses)

    # All-different constraints within each category
    problem.addConstraint(AllDifferentConstraint(), [("Name", n) for n in Names])
    problem.addConstraint(AllDifferentConstraint(), [("FavoriteSport", s) for s in FavoriteSports])
    problem.addConstraint(AllDifferentConstraint(), [("HairColor", hc) for hc in HairColors])
    problem.addConstraint(AllDifferentConstraint(), [("Height", h) for h in Heights])
    problem.addConstraint(AllDifferentConstraint(), [("Smoothie", sm) for sm in Smoothies])
    problem.addConstraint(AllDifferentConstraint(), [("Flower", f) for f in Flowers])

    # Clues:
    # 1. The person who loves soccer is not in the second house.
    problem.addConstraint(lambda x: x != 2, [("FavoriteSport", "soccer")])

    # 2. The Desert smoothie lover is directly left of the person who is very short.
    problem.addConstraint(lambda a, b: a + 1 == b, [("Smoothie", "desert"), ("Height", "very short")])

    # 3. The person who is very short is the person who has brown hair.
    problem.addConstraint(lambda a, b: a == b, [("Height", "very short"), ("HairColor", "brown")])

    # 4. The person who loves a carnations arrangement is the Desert smoothie lover.
    problem.addConstraint(lambda a, b: a == b, [("Flower", "carnations"), ("Smoothie", "desert")])

    # 5. Eric and the person who has brown hair are next to each other.
    problem.addConstraint(lambda a, b: abs(a - b) == 1, [("Name", "Eric"), ("HairColor", "brown")])

    solutions = problem.getSolutions()
    if not solutions:
        raise ValueError("No solution found for the given puzzle.")

    sol = solutions[0]

    def value_at_house(category, values, house):
        for v in values:
            if sol[(category, v)] == house:
                return v
        return None

    header = ["House", "Name", "FavoriteSport", "HairColor", "Height", "Smoothie", "Flower"]
    rows = []
    for hnum in sorted(houses):
        row = [
            str(hnum),
            value_at_house("Name", Names, hnum),
            value_at_house("FavoriteSport", FavoriteSports, hnum),
            value_at_house("HairColor", HairColors, hnum),
            value_at_house("Height", Heights, hnum),
            value_at_house("Smoothie", Smoothies, hnum),
            value_at_house("Flower", Flowers, hnum),
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()