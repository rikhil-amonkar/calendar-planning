import json
from z3 import Int, Solver, Distinct, And

def solve_puzzle():
    # Define houses
    houses = [1, 2]  # left to right

    # Define attributes and their codes
    Names = ["Eric", "Arnold"]
    Sports = ["basketball", "soccer"]
    Hobbies = ["photography", "gardening"]

    name_code = {n: i for i, n in enumerate(Names)}
    sport_code = {s: i for i, s in enumerate(Sports)}
    hobby_code = {h: i for i, h in enumerate(Hobbies)}

    N = len(houses)

    # Z3 variables: mapping each house to the code of its attribute
    name = [Int(f"name_{i+1}") for i in range(N)]
    sport = [Int(f"sport_{i+1}") for i in range(N)]
    hobby = [Int(f"hobby_{i+1}") for i in range(N)]

    s = Solver()

    # Domain constraints
    for i in range(N):
        s.add(name[i] >= 0, name[i] < len(Names))
        s.add(sport[i] >= 0, sport[i] < len(Sports))
        s.add(hobby[i] >= 0, hobby[i] < len(Hobbies))

    # Uniqueness constraints
    s.add(Distinct(name))
    s.add(Distinct(sport))
    s.add(Distinct(hobby))

    # Clue 1: The person who enjoys gardening is Arnold.
    for i in range(N):
        s.add((name[i] == name_code["Arnold"]) == (hobby[i] == hobby_code["gardening"]))

    # Clue 2: The photography enthusiast is not in the first house.
    s.add(hobby[0] != hobby_code["photography"])

    # Clue 3: The person who loves soccer is not in the first house.
    s.add(sport[0] != sport_code["soccer"])

    if s.check() != 1:  # 1 corresponds to sat
        raise RuntimeError("No solution found")

    m = s.model()

    # Build output in required JSON format
    rows = []
    for idx, house_num in enumerate(houses):
        row = [
            str(house_num),
            Names[m.eval(name[idx]).as_long()],
            Sports[m.eval(sport[idx]).as_long()],
            Hobbies[m.eval(hobby[idx]).as_long()],
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": ["House", "Name", "FavoriteSport", "Hobby"],
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))