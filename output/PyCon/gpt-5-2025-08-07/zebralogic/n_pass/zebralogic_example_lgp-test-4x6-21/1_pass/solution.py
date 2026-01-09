import json
from constraint import Problem, AllDifferentConstraint

def main():
    houses = [1, 2, 3, 4]

    names = ["Peter", "Arnold", "Alice", "Eric"]
    flowers = ["roses", "daffodils", "carnations", "lilies"]
    hobbies = ["photography", "painting", "cooking", "gardening"]
    pets = ["dog", "fish", "bird", "cat"]
    colors = ["red", "yellow", "green", "white"]
    styles = ["craftsman", "colonial", "ranch", "victorian"]

    def var_name(category, value):
        return f"{category}_{value}"

    problem = Problem()

    # Add variables
    for n in names:
        problem.addVariable(var_name("Name", n), houses)
    for f in flowers:
        problem.addVariable(var_name("Flower", f), houses)
    for h in hobbies:
        problem.addVariable(var_name("Hobby", h), houses)
    for p in pets:
        problem.addVariable(var_name("Pet", p), houses)
    for c in colors:
        problem.addVariable(var_name("Color", c), houses)
    for s in styles:
        problem.addVariable(var_name("Style", s), houses)

    # AllDifferent constraints per category
    problem.addConstraint(AllDifferentConstraint(), [var_name("Name", n) for n in names])
    problem.addConstraint(AllDifferentConstraint(), [var_name("Flower", f) for f in flowers])
    problem.addConstraint(AllDifferentConstraint(), [var_name("Hobby", h) for h in hobbies])
    problem.addConstraint(AllDifferentConstraint(), [var_name("Pet", p) for p in pets])
    problem.addConstraint(AllDifferentConstraint(), [var_name("Color", c) for c in colors])
    problem.addConstraint(AllDifferentConstraint(), [var_name("Style", s) for s in styles])

    # Helper to access variables
    N = lambda n: var_name("Name", n)
    F = lambda f: var_name("Flower", f)
    H = lambda h: var_name("Hobby", h)
    P = lambda p: var_name("Pet", p)
    C = lambda c: var_name("Color", c)
    S = lambda s: var_name("Style", s)

    # Apply constraints from clues

    # 1. The person in a Craftsman-style house is Arnold.
    problem.addConstraint(lambda a, b: a == b, (S("craftsman"), N("Arnold")))

    # 2. The person who loves the rose bouquet is somewhere to the right of Peter.
    problem.addConstraint(lambda r, p: r > p, (F("roses"), N("Peter")))

    # 3. The photography enthusiast is the person who owns a dog.
    problem.addConstraint(lambda ph, dg: ph == dg, (H("photography"), P("dog")))

    # 4. The person who loves a bouquet of daffodils is not in the fourth house.
    problem.addConstraint(lambda d: d != 4, (F("daffodils"),))

    # 5. The person who loves the rose bouquet is the person whose favorite color is red.
    problem.addConstraint(lambda r_fl, r_col: r_fl == r_col, (F("roses"), C("red")))

    # 6. The person in a Craftsman-style house is in the second house.
    problem.addConstraint(lambda s: s == 2, (S("craftsman"),))

    # 7. Eric is the person residing in a Victorian house.
    problem.addConstraint(lambda e, v: e == v, (N("Eric"), S("victorian")))

    # 8. The person with an aquarium of fish is the person who loves white.
    problem.addConstraint(lambda fish, white: fish == white, (P("fish"), C("white")))

    # 9. The person who loves cooking is somewhere to the right of the person whose favorite color is red.
    problem.addConstraint(lambda cook, red: cook > red, (H("cooking"), C("red")))

    # 10. The person who loves white is the person who loves a carnations arrangement.
    problem.addConstraint(lambda white, carn: white == carn, (C("white"), F("carnations")))

    # 11. The person who loves white is somewhere to the right of the person who enjoys gardening.
    problem.addConstraint(lambda white, gard: white > gard, (C("white"), H("gardening")))

    # 12. The person who loves a bouquet of daffodils is the person who loves yellow.
    problem.addConstraint(lambda daff, yellow: daff == yellow, (F("daffodils"), C("yellow")))

    # 13. The person living in a colonial-style house is the person whose favorite color is red.
    problem.addConstraint(lambda col_style, red_col: col_style == red_col, (S("colonial"), C("red")))

    # 14. The person who has a cat is Eric.
    problem.addConstraint(lambda cat, eric: cat == eric, (P("cat"), N("Eric")))

    solutions = problem.getSolutions()

    if not solutions:
        raise ValueError("No solution found for the puzzle.")

    # Assuming unique solution; select the first
    sol = solutions[0]

    # Invert mapping: get attribute value per house index
    def invert(category_values, prefix):
        # returns dict house_index -> value_name
        inv = {}
        for val in category_values:
            inv[sol[var_name(prefix, val)]] = val
        return inv

    house_to_name = invert(names, "Name")
    house_to_flower = invert(flowers, "Flower")
    house_to_hobby = invert(hobbies, "Hobby")
    house_to_pet = invert(pets, "Pet")
    house_to_color = invert(colors, "Color")
    house_to_style = invert(styles, "Style")

    header = ["House", "Name", "Flower", "Hobby", "Pet", "Color", "HouseStyle"]
    rows = []
    for h in sorted(houses):
        row = [
            str(h),
            house_to_name[h],
            house_to_flower[h],
            house_to_hobby[h],
            house_to_pet[h],
            house_to_color[h],
            house_to_style[h],
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()