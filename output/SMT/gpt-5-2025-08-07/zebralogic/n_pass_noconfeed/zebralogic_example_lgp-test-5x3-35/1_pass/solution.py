import json
from z3 import Solver, Int, And, Or, Distinct

def main():
    # Define attributes
    names = ["Eric", "Peter", "Arnold", "Alice", "Bob"]
    mothers = ["Kailyn", "Janelle", "Aniya", "Penny", "Holly"]
    heights = ["average", "very short", "short", "very tall", "tall"]

    name_idx = {n: i for i, n in enumerate(names)}
    mother_idx = {m: i for i, m in enumerate(mothers)}
    height_idx = {h: i for i, h in enumerate(heights)}

    # Position variables for each attribute value (1..5)
    pos_name = [Int(f"pos_name_{i}") for i in range(5)]
    pos_mother = [Int(f"pos_mother_{i}") for i in range(5)]
    pos_height = [Int(f"pos_height_{i}") for i in range(5)]

    s = Solver()

    # Domain constraints: positions are 1..5
    for arr in (pos_name, pos_mother, pos_height):
        for v in arr:
            s.add(And(v >= 1, v <= 5))

    # AllDifferent constraints for bijection
    s.add(Distinct(*pos_name))
    s.add(Distinct(*pos_mother))
    s.add(Distinct(*pos_height))

    # Clues as constraints:

    # 1. Alice is The person whose mother's name is Aniya.
    s.add(pos_name[name_idx["Alice"]] == pos_mother[mother_idx["Aniya"]])

    # 2. The person who has an average height is somewhere to the left of Penny's child.
    s.add(pos_height[height_idx["average"]] < pos_mother[mother_idx["Penny"]])

    # 3. The person whose mother's name is Janelle is Bob.
    s.add(pos_mother[mother_idx["Janelle"]] == pos_name[name_idx["Bob"]])

    # 4. Peter is not in the second house.
    s.add(pos_name[name_idx["Peter"]] != 2)

    # 5. The person who is short is directly left of Arnold.
    s.add(pos_height[height_idx["short"]] + 1 == pos_name[name_idx["Arnold"]])

    # 6. The person who is very tall is Arnold.
    s.add(pos_height[height_idx["very tall"]] == pos_name[name_idx["Arnold"]])

    # 7. Bob is directly left of the person who has an average height.
    s.add(pos_name[name_idx["Bob"]] + 1 == pos_height[height_idx["average"]])

    # 8. Eric is not in the fifth house.
    s.add(pos_name[name_idx["Eric"]] != 5)

    # 9. The person who is very tall is somewhere to the right of Holly's child.
    s.add(pos_height[height_idx["very tall"]] > pos_mother[mother_idx["Holly"]])

    # 10. Eric is The person whose mother's name is Kailyn.
    s.add(pos_name[name_idx["Eric"]] == pos_mother[mother_idx["Kailyn"]])

    # 11. The person who is very short is in the fifth house.
    s.add(pos_height[height_idx["very short"]] == 5)

    if s.check() != 1:  # sat
        result = {
            "solution": {
                "header": ["House", "Name", "Mother", "Height"],
                "rows": []
            }
        }
        print(json.dumps(result))
        return

    m = s.model()

    # Build inverse mapping from house -> attribute
    house_to_name = {}
    house_to_mother = {}
    house_to_height = {}

    for i, v in enumerate(pos_name):
        house = m.evaluate(v).as_long()
        house_to_name[house] = names[i]

    for i, v in enumerate(pos_mother):
        house = m.evaluate(v).as_long()
        house_to_mother[house] = mothers[i]

    for i, v in enumerate(pos_height):
        house = m.evaluate(v).as_long()
        house_to_height[house] = heights[i]

    rows = []
    for house in range(1, 6):
        row = [
            str(house),
            house_to_name[house],
            house_to_mother[house],
            house_to_height[house],
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": ["House", "Name", "Mother", "Height"],
            "rows": rows
        }
    }

    print(json.dumps(output))

if __name__ == "__main__":
    main()