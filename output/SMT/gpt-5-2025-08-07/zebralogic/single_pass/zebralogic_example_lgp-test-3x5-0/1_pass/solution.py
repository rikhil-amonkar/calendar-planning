import json
from z3 import Solver, Int, And, Distinct, sat

def solve_puzzle():
    # Define categories and their values
    categories = {
        "Name": ["Peter", "Arnold", "Eric"],
        "BookGenre": ["science fiction", "mystery", "romance"],
        "Smoothie": ["watermelon", "desert", "cherry"],
        "Birthday": ["april", "jan", "sept"],
        "Height": ["average", "very short", "short"],
    }

    # Create Z3 variables for each value indicating the house number (1..3)
    vars_by_cat = {
        cat: {val: Int(f"{cat}_{val.replace(' ', '_')}") for val in values}
        for cat, values in categories.items()
    }

    s = Solver()

    # Domain and AllDifferent constraints per category
    for cat, mapping in vars_by_cat.items():
        for v in mapping.values():
            s.add(And(v >= 1, v <= 3))
        s.add(Distinct(list(mapping.values())))

    # Clues:
    # 1. The person who likes Cherry smoothies is not in the second house.
    s.add(vars_by_cat["Smoothie"]["cherry"] != 2)

    # 2. Arnold is the person who loves mystery books.
    s.add(vars_by_cat["Name"]["Arnold"] == vars_by_cat["BookGenre"]["mystery"])

    # 3. The person whose birthday is in January is not in the first house.
    s.add(vars_by_cat["Birthday"]["jan"] != 1)

    # 4. The person who is very short is the person who loves romance books.
    s.add(vars_by_cat["Height"]["very short"] == vars_by_cat["BookGenre"]["romance"])

    # 5. The person who loves mystery books is the person whose birthday is in September.
    s.add(vars_by_cat["BookGenre"]["mystery"] == vars_by_cat["Birthday"]["sept"])

    # 6. The person who has an average height is the Desert smoothie lover.
    s.add(vars_by_cat["Height"]["average"] == vars_by_cat["Smoothie"]["desert"])

    # 7. Eric is in the first house.
    s.add(vars_by_cat["Name"]["Eric"] == 1)

    # 8. The Watermelon smoothie lover is the person who is short.
    s.add(vars_by_cat["Smoothie"]["watermelon"] == vars_by_cat["Height"]["short"])

    # 9. The Watermelon smoothie lover is Eric.
    s.add(vars_by_cat["Smoothie"]["watermelon"] == vars_by_cat["Name"]["Eric"])

    if s.check() != sat:
        raise RuntimeError("No solution found")

    m = s.model()

    def value_for_house(mapping, house):
        for label, var in mapping.items():
            if m.evaluate(var).as_long() == house:
                return label
        raise RuntimeError("No value found for house")

    header = ["House", "Name", "BookGenre", "Smoothie", "Birthday", "Height"]
    rows = []
    for house in [1, 2, 3]:
        row = [
            str(house),
            value_for_house(vars_by_cat["Name"], house),
            value_for_house(vars_by_cat["BookGenre"], house),
            value_for_house(vars_by_cat["Smoothie"], house),
            value_for_house(vars_by_cat["Birthday"], house),
            value_for_house(vars_by_cat["Height"], house),
        ]
        rows.append(row)

    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()