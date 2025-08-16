import json
from z3 import *

def solve_puzzle():
    # Indices for attributes
    names = ["Arnold", "Peter", "Eric", "Alice", "Bob"]
    hobbies = ["painting", "cooking", "knitting", "gardening", "photography"]
    heights = ["very tall", "tall", "very short", "average", "short"]
    foods = ["stew", "grilled cheese", "stir fry", "spaghetti", "pizza"]

    N = 5  # houses 1..5

    # Variables: position (house number 1..5) for each attribute value
    NamePos = [Int(f"NamePos_{n}") for n in names]
    HobbyPos = [Int(f"HobbyPos_{h}") for h in hobbies]
    HeightPos = [Int(f"HeightPos_{h}") for h in heights]
    FoodPos = [Int(f"FoodPos_{f}") for f in foods]

    s = Solver()

    # Domain constraints
    for arr in (NamePos, HobbyPos, HeightPos, FoodPos):
        for v in arr:
            s.add(And(v >= 1, v <= N))

    # Uniqueness constraints
    s.add(Distinct(NamePos))
    s.add(Distinct(HobbyPos))
    s.add(Distinct(HeightPos))
    s.add(Distinct(FoodPos))

    # Helper to get indices
    idx_name = {n: i for i, n in enumerate(names)}
    idx_hobby = {h: i for i, h in enumerate(hobbies)}
    idx_height = {h: i for i, h in enumerate(heights)}
    idx_food = {f: i for i, f in enumerate(foods)}

    # Clues:
    # 1. Bob is the photography enthusiast.
    s.add(NamePos[idx_name["Bob"]] == HobbyPos[idx_hobby["photography"]])

    # 2. The person who loves eating grilled cheese is the person who is tall.
    s.add(FoodPos[idx_food["grilled cheese"]] == HeightPos[idx_height["tall"]])

    # 3. Peter is not in the second house.
    s.add(NamePos[idx_name["Peter"]] != 2)

    # 4. The person who is tall is directly left of the person who loves stir fry.
    s.add(HeightPos[idx_height["tall"]] == FoodPos[idx_food["stir fry"]] - 1)

    # 5. The person who loves cooking is the person who has an average height.
    s.add(HobbyPos[idx_hobby["cooking"]] == HeightPos[idx_height["average"]])

    # 6. Alice is directly left of the person who is a pizza lover.
    s.add(NamePos[idx_name["Alice"]] == FoodPos[idx_food["pizza"]] - 1)

    # 7. (Interpreted) The spaghetti eater is not in the second house.
    s.add(FoodPos[idx_food["spaghetti"]] != 2)

    # 8. Eric is not in the fifth house.
    s.add(NamePos[idx_name["Eric"]] != 5)

    # 9. The person who is short is Peter.
    s.add(HeightPos[idx_height["short"]] == NamePos[idx_name["Peter"]])

    # 10. The person who has an average height and the person who enjoys gardening are next to each other.
    s.add(Abs(HeightPos[idx_height["average"]] - HobbyPos[idx_hobby["gardening"]]) == 1)

    # 11. The person who paints as a hobby is directly left of the person who loves eating grilled cheese.
    s.add(HobbyPos[idx_hobby["painting"]] == FoodPos[idx_food["grilled cheese"]] - 1)

    # 12. The person who is very short is in the fifth house.
    s.add(HeightPos[idx_height["very short"]] == 5)

    # 13. The person who is tall is in the third house.
    s.add(HeightPos[idx_height["tall"]] == 3)

    # 14. Alice is somewhere to the right of the photography enthusiast.
    # Since Bob is the photography enthusiast (clue 1), this is: Alice to the right of Bob.
    s.add(NamePos[idx_name["Alice"]] > NamePos[idx_name["Bob"]])

    if s.check() != sat:
        raise RuntimeError("Puzzle is unsatisfiable")

    m = s.model()

    # Build reverse maps from house -> attribute value index
    house_to_name = {}
    house_to_hobby = {}
    house_to_height = {}
    house_to_food = {}

    for i, v in enumerate(NamePos):
        house_to_name[m[v].as_long()] = names[i]
    for i, v in enumerate(HobbyPos):
        house_to_hobby[m[v].as_long()] = hobbies[i]
    for i, v in enumerate(HeightPos):
        house_to_height[m[v].as_long()] = heights[i]
    for i, v in enumerate(FoodPos):
        house_to_food[m[v].as_long()] = foods[i]

    # Prepare JSON output
    header = ["House", "Name", "Hobby", "Height", "Food"]
    rows = []
    for house in range(1, N + 1):
        rows.append([
            str(house),
            house_to_name[house],
            house_to_hobby[house],
            house_to_height[house],
            house_to_food[house],
        ])

    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, ensure_ascii=False, indent=2))