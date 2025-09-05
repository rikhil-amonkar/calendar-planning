import json
from z3 import *

def main():
    # Houses
    HOUSES = 2
    house_ids = list(range(1, HOUSES + 1))

    # Categories and values
    Names = ["Arnold", "Eric"]
    Foods = ["grilled cheese", "pizza"]
    Mothers = ["Holly", "Aniya"]

    # Helper to create position variables for each item in a category
    def create_pos_vars(items, prefix):
        return {item: Int(f"{prefix}_{item.replace(' ', '_')}") for item in items}

    pos_name = create_pos_vars(Names, "pos_name")
    pos_food = create_pos_vars(Foods, "pos_food")
    pos_mother = create_pos_vars(Mothers, "pos_mother")

    s = Solver()

    # Domain constraints: each position is a house number 1..HOUSES
    for d in [pos_name, pos_food, pos_mother]:
        for v in d.values():
            s.add(And(v >= 1, v <= HOUSES))

    # Uniqueness within each category
    s.add(Distinct(list(pos_name.values())))
    s.add(Distinct(list(pos_food.values())))
    s.add(Distinct(list(pos_mother.values())))

    # Clue 1: grilled cheese is directly left of pizza
    s.add(pos_food["grilled cheese"] + 1 == pos_food["pizza"])

    # Clue 2: Arnold is not in the second house
    s.add(pos_name["Arnold"] != 2)

    # Clue 3: Arnold is the person whose mother's name is Holly
    s.add(pos_name["Arnold"] == pos_mother["Holly"])

    if s.check() != sat:
        raise RuntimeError("Puzzle is unsatisfiable")

    m = s.model()

    # Build solution rows per house
    rows = []
    for h in house_ids:
        # Find assigned values for each category at house h
        name_at_h = next(name for name, var in pos_name.items() if m[var].as_long() == h)
        food_at_h = next(food for food, var in pos_food.items() if m[var].as_long() == h)
        mother_at_h = next(mother for mother, var in pos_mother.items() if m[var].as_long() == h)

        rows.append([str(h), name_at_h, food_at_h, mother_at_h])

    output = {
        "solution": {
            "header": ["House", "Name", "Food", "Mother"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()