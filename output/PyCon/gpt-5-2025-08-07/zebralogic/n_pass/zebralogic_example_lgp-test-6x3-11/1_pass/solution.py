import json
from constraint import Problem, AllDifferentConstraint

def main():
    houses = list(range(1, 7))

    names = ['Bob', 'Peter', 'Eric', 'Alice', 'Arnold', 'Carol']
    hair_colors = ['auburn', 'blonde', 'brown', 'black', 'red', 'gray']
    heights = ['very tall', 'average', 'very short', 'tall', 'super tall', 'short']

    problem = Problem()

    # Create variables for each attribute value representing the house position (1..6)
    for n in names:
        problem.addVariable(f"Name_{n}", houses)
    for c in hair_colors:
        problem.addVariable(f"Hair_{c}", houses)
    for h in heights:
        problem.addVariable(f"Height_{h}", houses)

    # All-different constraints within each category
    problem.addConstraint(AllDifferentConstraint(), [f"Name_{n}" for n in names])
    problem.addConstraint(AllDifferentConstraint(), [f"Hair_{c}" for c in hair_colors])
    problem.addConstraint(AllDifferentConstraint(), [f"Height_{h}" for h in heights])

    # Clues as constraints:

    # 1. The person who has blonde hair is directly left of Bob.
    problem.addConstraint(
        lambda blonde, bob: blonde + 1 == bob,
        ["Hair_blonde", "Name_Bob"]
    )

    # 2. Alice is in the fourth house.
    problem.addConstraint(lambda x: x == 4, ["Name_Alice"])

    # 3. The person who is short is Arnold.
    problem.addConstraint(lambda short, arnold: short == arnold, ["Height_short", "Name_Arnold"])

    # 4. The person who is tall is in the sixth house.
    problem.addConstraint(lambda x: x == 6, ["Height_tall"])

    # 5. The person who has black hair is not in the fourth house.
    problem.addConstraint(lambda x: x != 4, ["Hair_black"])

    # 6. The person who has red hair is Eric.
    problem.addConstraint(lambda red, eric: red == eric, ["Hair_red", "Name_Eric"])

    # 7. The person who is super tall is somewhere to the right of the person who has an average height.
    problem.addConstraint(lambda st, av: st > av, ["Height_super tall", "Height_average"])

    # 8. The person who has blonde hair is Carol.
    problem.addConstraint(lambda blonde, carol: blonde == carol, ["Hair_blonde", "Name_Carol"])

    # 9. There is one house between the person who has gray hair and the person who has red hair.
    problem.addConstraint(lambda gray, red: abs(gray - red) == 2, ["Hair_gray", "Hair_red"])

    # 10. The person who is very short is in the fifth house.
    problem.addConstraint(lambda x: x == 5, ["Height_very short"])

    # 11. Bob is the person who has brown hair.
    problem.addConstraint(lambda brown, bob: brown == bob, ["Hair_brown", "Name_Bob"])

    # 12. The person who has gray hair is in the third house.
    problem.addConstraint(lambda x: x == 3, ["Hair_gray"])

    # 13. The person who has blonde hair is the person who is very tall.
    problem.addConstraint(lambda blonde, vt: blonde == vt, ["Hair_blonde", "Height_very tall"])

    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No solution found for the given puzzle constraints.")

    sol = solutions[0]

    # Build mappings from attribute to house position
    name_pos = {n: sol[f"Name_{n}"] for n in names}
    hair_pos = {c: sol[f"Hair_{c}"] for c in hair_colors}
    height_pos = {h: sol[f"Height_{h}"] for h in heights}

    # Build reverse lookups to get attribute by house
    house_to_name = {pos: n for n, pos in name_pos.items()}
    house_to_hair = {pos: c for c, pos in hair_pos.items()}
    house_to_height = {pos: h for h, pos in height_pos.items()}

    result = {
        "solution": {
            "header": ["House", "Name", "HairColor", "Height"],
            "rows": []
        }
    }

    for house in range(1, 7):
        row = [
            str(house),
            house_to_name[house],
            house_to_hair[house],
            house_to_height[house]
        ]
        result["solution"]["rows"].append(row)

    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()