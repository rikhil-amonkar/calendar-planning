import json
from z3 import Solver, Int, Distinct, And, Or, Abs

def solve_puzzle():
    houses = [1, 2, 3, 4]

    Names = ["Eric", "Alice", "Peter", "Arnold"]
    Smoothies = ["dragonfruit", "cherry", "desert", "watermelon"]
    Sports = ["soccer", "tennis", "basketball", "swimming"]
    Cars = ["tesla model 3", "toyota camry", "honda civic", "ford f150"]
    Flowers = ["daffodils", "roses", "lilies", "carnations"]

    # Create position variables (1..4) for each value in each category
    def make_vars(items, prefix):
        return {item: Int(f"{prefix}_{item.replace(' ', '_')}") for item in items}

    pos_name = make_vars(Names, "name")
    pos_smoothie = make_vars(Smoothies, "smoothie")
    pos_sport = make_vars(Sports, "sport")
    pos_car = make_vars(Cars, "car")
    pos_flower = make_vars(Flowers, "flower")

    s = Solver()

    # Domain constraints: all positions are in 1..4
    for d in [pos_name, pos_smoothie, pos_sport, pos_car, pos_flower]:
        for v in d.values():
            s.add(And(v >= 1, v <= 4))

    # All-different constraints within each category
    s.add(Distinct([pos_name[n] for n in Names]))
    s.add(Distinct([pos_smoothie[x] for x in Smoothies]))
    s.add(Distinct([pos_sport[x] for x in Sports]))
    s.add(Distinct([pos_car[x] for x in Cars]))
    s.add(Distinct([pos_flower[x] for x in Flowers]))

    # Clues:
    # 1. Tesla Model 3 owner loves roses
    s.add(pos_car["tesla model 3"] == pos_flower["roses"])

    # 2. Peter loves dragonfruit smoothie
    s.add(pos_name["Peter"] == pos_smoothie["dragonfruit"])

    # 3. Desert smoothie lover owns a Toyota Camry
    s.add(pos_smoothie["desert"] == pos_car["toyota camry"])

    # 4. Tennis is in the first house
    s.add(pos_sport["tennis"] == 1)

    # 5. Toyota Camry owner and basketball lover are next to each other
    s.add(Abs(pos_car["toyota camry"] - pos_sport["basketball"]) == 1)

    # 6. Arnold loves basketball
    s.add(pos_name["Arnold"] == pos_sport["basketball"])

    # 7. Honda Civic owner loves daffodils
    s.add(pos_car["honda civic"] == pos_flower["daffodils"])

    # 8. Eric loves roses
    s.add(pos_name["Eric"] == pos_flower["roses"])

    # 9. Watermelon smoothie lover is not in the first house
    s.add(pos_smoothie["watermelon"] != 1)

    # 10. Honda Civic owner is to the right of the Desert smoothie lover
    s.add(pos_car["honda civic"] > pos_smoothie["desert"])

    # 11. Basketball lover loves lilies
    s.add(pos_sport["basketball"] == pos_flower["lilies"])

    # 12. Tennis lover and soccer lover are next to each other
    s.add(Abs(pos_sport["tennis"] - pos_sport["soccer"]) == 1)

    if s.check() != 1:  # 1 corresponds to sat
        raise RuntimeError("No solution found")

    m = s.model()

    # Helper to invert position mapping: given position -> item
    def item_at_pos(pos_dict, pos):
        for k, v in pos_dict.items():
            if m[v].as_long() == pos:
                return k
        return None

    header = ["House", "Name", "Smoothie", "FavoriteSport", "CarModel", "Flower"]
    rows = []
    for h in houses:
        row = [
            str(h),
            item_at_pos(pos_name, h),
            item_at_pos(pos_smoothie, h),
            item_at_pos(pos_sport, h),
            item_at_pos(pos_car, h),
            item_at_pos(pos_flower, h),
        ]
        rows.append(row)

    return {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False))