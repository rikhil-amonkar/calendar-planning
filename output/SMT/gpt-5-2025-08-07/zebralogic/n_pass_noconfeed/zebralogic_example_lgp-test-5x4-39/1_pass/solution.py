import json
from z3 import Int, Solver, Distinct, And, Or

def main():
    # Domains
    names = ["Arnold", "Peter", "Eric", "Alice", "Bob"]
    hobbies = ["painting", "cooking", "knitting", "gardening", "photography"]
    heights = ["very tall", "tall", "very short", "average", "short"]
    foods = ["stew", "grilled cheese", "stir fry", "spaghetti", "pizza"]

    # Index helpers
    name_idx = {n: i for i, n in enumerate(names)}
    hobby_idx = {h: i for i, h in enumerate(hobbies)}
    height_idx = {h: i for i, h in enumerate(heights)}
    food_idx = {f: i for i, f in enumerate(foods)}

    # Position variables: position of each attribute (1..5)
    pos_name = {n: Int(f"pos_name_{n}") for n in names}
    pos_hobby = {h: Int(f"pos_hobby_{h}") for h in hobbies}
    pos_height = {h: Int(f"pos_height_{h}") for h in heights}
    pos_food = {f: Int(f"pos_food_{f}") for f in foods}

    s = Solver()

    # Domains: 1..5
    for arr in [pos_name, pos_hobby, pos_height, pos_food]:
        for v in arr.values():
            s.add(And(v >= 1, v <= 5))

    # AllDifferent within each category
    s.add(Distinct([pos_name[n] for n in names]))
    s.add(Distinct([pos_hobby[h] for h in hobbies]))
    s.add(Distinct([pos_height[h] for h in heights]))
    s.add(Distinct([pos_food[f] for f in foods]))

    # Clues:
    # 1. Bob is the photography enthusiast.
    s.add(pos_name["Bob"] == pos_hobby["photography"])

    # 2. The person who loves eating grilled cheese is the person who is tall.
    s.add(pos_food["grilled cheese"] == pos_height["tall"])

    # 3. Peter is not in the second house.
    s.add(pos_name["Peter"] != 2)

    # 4. The person who is tall is directly left of the person who loves stir fry.
    s.add(pos_height["tall"] + 1 == pos_food["stir fry"])

    # 5. The person who loves cooking is the person who has an average height.
    s.add(pos_hobby["cooking"] == pos_height["average"])

    # 6. Alice is directly left of the person who is a pizza lover.
    s.add(pos_name["Alice"] + 1 == pos_food["pizza"])

    # 7. Interpreted as: The spaghetti eater is not in the second house.
    s.add(pos_food["spaghetti"] != 2)

    # 8. Eric is not in the fifth house.
    s.add(pos_name["Eric"] != 5)

    # 9. The person who is short is Peter.
    s.add(pos_height["short"] == pos_name["Peter"])

    # 10. The person with average height and the person who enjoys gardening are next to each other.
    s.add(Or(pos_height["average"] - pos_hobby["gardening"] == 1,
             pos_hobby["gardening"] - pos_height["average"] == 1))

    # 11. The painter is directly left of the grilled cheese eater.
    s.add(pos_hobby["painting"] + 1 == pos_food["grilled cheese"])

    # 12. The person who is very short is in the fifth house.
    s.add(pos_height["very short"] == 5)

    # 13. The person who is tall is in the third house.
    s.add(pos_height["tall"] == 3)

    # 14. Alice is somewhere to the right of the photography enthusiast.
    s.add(pos_name["Alice"] > pos_hobby["photography"])

    # Solve
    if s.check() != 1:  # sat
        # Fallback empty solution if unsat (should not happen with consistent puzzle)
        result = {
            "solution": {
                "header": ["House", "Name", "Hobby", "Height", "Food"],
                "rows": [[str(i), "", "", "", ""] for i in range(1, 6)]
            }
        }
        print(json.dumps(result))
        return

    m = s.model()

    # Build inverse mappings: house -> attribute string
    house_to_name = {}
    for n in names:
        house_to_name[m[pos_name[n]].as_long()] = n

    house_to_hobby = {}
    for h in hobbies:
        house_to_hobby[m[pos_hobby[h]].as_long()] = h

    house_to_height = {}
    for h in heights:
        house_to_height[m[pos_height[h]].as_long()] = h

    house_to_food = {}
    for f in foods:
        house_to_food[m[pos_food[f]].as_long()] = f

    rows = []
    for house in range(1, 6):
        row = [
            str(house),
            house_to_name[house],
            house_to_hobby[house],
            house_to_height[house],
            house_to_food[house],
        ]
        rows.append(row)

    result = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Height", "Food"],
            "rows": rows
        }
    }

    print(json.dumps(result, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()