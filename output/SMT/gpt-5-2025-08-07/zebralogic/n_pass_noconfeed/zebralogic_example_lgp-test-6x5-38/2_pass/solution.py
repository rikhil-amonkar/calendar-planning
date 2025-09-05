import json
from z3 import Int, Solver, Distinct, And, Abs, sat

def main():
    houses = range(1, 7)

    # Categories and their items
    Names = ["Arnold", "Carol", "Eric", "Bob", "Alice", "Peter"]
    Birthdays = ["feb", "mar", "sept", "jan", "may", "april"]
    Foods = ["stew", "soup", "grilled cheese", "stir fry", "spaghetti", "pizza"]
    Heights = ["very short", "average", "super tall", "short", "very tall", "tall"]
    Cars = ["chevrolet silverado", "ford f150", "bmw 3 series", "tesla model 3", "toyota camry", "honda civic"]

    # Create Z3 variables for positions of each attribute (position 1..6)
    def make_pos_vars(items, prefix):
        return {item: Int(f"{prefix}_{item}".replace(" ", "_").replace("-", "_")) for item in items}

    pos_name = make_pos_vars(Names, "pos_name")
    pos_bday = make_pos_vars(Birthdays, "pos_bday")
    pos_food = make_pos_vars(Foods, "pos_food")
    pos_height = make_pos_vars(Heights, "pos_height")
    pos_car = make_pos_vars(Cars, "pos_car")

    s = Solver()

    # Domain constraints: each position in 1..6
    for d in [pos_name, pos_bday, pos_food, pos_height, pos_car]:
        for v in d.values():
            s.add(And(v >= 1, v <= 6))
        # Uniqueness within each category
        s.add(Distinct(list(d.values())))

    # Helper references
    N = pos_name
    B = pos_bday
    F = pos_food
    H = pos_height
    C = pos_car

    # Clues:

    # 1. The person who owns a Honda Civic is the person who is short.
    s.add(C["honda civic"] == H["short"])

    # 2. The person who owns a Ford F-150 is in the fifth house.
    s.add(C["ford f150"] == 5)

    # 3. The person who loves stir fry is somewhere to the left of Eric.
    s.add(F["stir fry"] < N["Eric"])

    # 4. The person whose birthday is in May is somewhere to the left of Carol.
    s.add(B["may"] < N["Carol"])

    # 5. The person who is very short is somewhere to the left of the person whose birthday is in April.
    s.add(H["very short"] < B["april"])

    # 6. The person who owns a BMW 3 Series is not in the third house.
    s.add(C["bmw 3 series"] != 3)

    # 7. There are two houses between the person who loves stir fry and the person who is a pizza lover.
    s.add(Abs(F["stir fry"] - F["pizza"]) == 3)

    # 8. The person who loves the soup is directly left of Eric.
    s.add(F["soup"] + 1 == N["Eric"])

    # 9. The spaghetti eater and the person whose birthday is in May are next to each other.
    s.add(Abs(F["spaghetti"] - B["may"]) == 1)

    # 10. Alice is directly left of the person who owns a BMW 3 Series.
    s.add(N["Alice"] + 1 == C["bmw 3 series"])

    # 11. The person who owns a Tesla Model 3 is somewhere to the left of the person who is tall.
    s.add(C["tesla model 3"] < H["tall"])

    # 12. The person who is very tall is the person who owns a Toyota Camry.
    s.add(H["very tall"] == C["toyota camry"])

    # 13. Peter is directly left of the person who is a pizza lover.
    s.add(N["Peter"] + 1 == F["pizza"])

    # 14. The person who loves the stew is not in the third house.
    s.add(F["stew"] != 3)

    # 15. There is one house between the person whose birthday is in September and the person who is very short.
    s.add(Abs(B["sept"] - H["very short"]) == 2)

    # 16. There is one house between the person whose birthday is in March and the person who is super tall.
    s.add(Abs(B["mar"] - H["super tall"]) == 2)

    # 17. The person who is tall is Bob.
    s.add(H["tall"] == N["Bob"])

    # 18. The person whose birthday is in May is somewhere to the right of Alice.
    s.add(B["may"] > N["Alice"])

    # 19. The person who is very short is in the fourth house.
    s.add(H["very short"] == 4)

    # 20. The person whose birthday is in March is the person who is short.
    s.add(B["mar"] == H["short"])

    # 21. Carol is the person who owns a Tesla Model 3.
    s.add(N["Carol"] == C["tesla model 3"])

    # 22. Eric is the person whose birthday is in January.
    s.add(N["Eric"] == B["jan"])

    res = s.check()
    if res != sat:
        print(json.dumps({"status": str(res), "message": "No solution found"}, indent=2))
        return

    m = s.model()

    # Build inverse maps: position -> item
    def invert(pos_map):
        inv = {}
        for k, v in pos_map.items():
            inv[m[v].as_long()] = k
        return inv

    inv_name = invert(pos_name)
    inv_bday = invert(pos_bday)
    inv_food = invert(pos_food)
    inv_height = invert(pos_height)
    inv_car = invert(pos_car)

    rows = []
    for h in houses:
        row = [
            str(h),
            inv_name[h],
            inv_bday[h],
            inv_food[h],
            inv_height[h],
            inv_car[h],
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": ["House", "Name", "Birthday", "Food", "Height", "CarModel"],
            "rows": rows
        }
    }
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()