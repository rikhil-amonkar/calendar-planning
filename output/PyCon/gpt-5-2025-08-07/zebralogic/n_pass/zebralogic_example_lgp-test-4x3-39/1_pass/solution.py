import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define domains
    houses = [1, 2, 3, 4]
    names = ["Eric", "Alice", "Peter", "Arnold"]
    hairs = ["blonde", "black", "red", "brown"]
    sports = ["swimming", "soccer", "basketball", "tennis"]

    # Initialize problem
    problem = Problem()

    # Create variables for each category mapping to house positions
    name_vars = {name: f"Name_{name}" for name in names}
    hair_vars = {hair: f"Hair_{hair}" for hair in hairs}
    sport_vars = {sport: f"Sport_{sport}" for sport in sports}

    problem.addVariables(list(name_vars.values()), houses)
    problem.addVariables(list(hair_vars.values()), houses)
    problem.addVariables(list(sport_vars.values()), houses)

    # AllDifferent constraints for each category
    problem.addConstraint(AllDifferentConstraint(), list(name_vars.values()))
    problem.addConstraint(AllDifferentConstraint(), list(hair_vars.values()))
    problem.addConstraint(AllDifferentConstraint(), list(sport_vars.values()))

    # Constraints from clues

    # 1. The person who loves soccer is not in the second house.
    problem.addConstraint(lambda s: s != 2, (sport_vars["soccer"],))

    # 2. Eric is the person who has blonde hair.
    problem.addConstraint(lambda n, h: n == h, (name_vars["Eric"], hair_vars["blonde"]))

    # 3. The person who has blonde hair is somewhere to the right of the person who loves basketball.
    problem.addConstraint(lambda hb, sb: hb > sb, (hair_vars["blonde"], sport_vars["basketball"]))

    # 4. The person who has black hair is the person who loves tennis.
    problem.addConstraint(lambda hb, st: hb == st, (hair_vars["black"], sport_vars["tennis"]))

    # 5. Arnold is somewhere to the left of the person who has red hair.
    problem.addConstraint(lambda na, hr: na < hr, (name_vars["Arnold"], hair_vars["red"]))

    # 6. Alice is the person who loves swimming.
    problem.addConstraint(lambda n, s: n == s, (name_vars["Alice"], sport_vars["swimming"]))

    # 7. The person who has red hair is directly left of the person who has black hair.
    problem.addConstraint(lambda hr, hb: hr + 1 == hb, (hair_vars["red"], hair_vars["black"]))

    # Solve
    solutions = problem.getSolutions()
    if not solutions:
        result = {
            "solution": {
                "header": ["House", "Name", "HairColor", "FavoriteSport"],
                "rows": []
            }
        }
        print(json.dumps(result))
        return

    sol = solutions[0]

    # Build output rows in house order
    pos_to_name = {sol[name_vars[n]]: n for n in names}
    pos_to_hair = {sol[hair_vars[h]]: h for h in hairs}
    pos_to_sport = {sol[sport_vars[s]]: s for s in sports}

    rows = []
    for house in sorted(houses):
        rows.append([
            str(house),
            pos_to_name[house],
            pos_to_hair[house],
            pos_to_sport[house]
        ])

    result = {
        "solution": {
            "header": ["House", "Name", "HairColor", "FavoriteSport"],
            "rows": rows
        }
    }
    print(json.dumps(result))

if __name__ == "__main__":
    main()