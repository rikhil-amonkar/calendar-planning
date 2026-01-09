import json
from constraint import Problem, AllDifferentConstraint

def main():
    houses = [1, 2, 3, 4, 5]

    categories = {
        "Name": ["Bob", "Arnold", "Peter", "Alice", "Eric"],
        "Drink": ["milk", "root beer", "coffee", "tea", "water"],
        "Color": ["blue", "green", "white", "yellow", "red"],
        "Flower": ["daffodils", "roses", "lilies", "tulips", "carnations"],
        "Hobby": ["painting", "cooking", "photography", "gardening", "knitting"],
    }

    # Helper to sanitize variable names (internal use only)
    def var_name(category, value):
        return f"{category}_{value.replace(' ', '_')}"

    # Build variable map
    var_map = {cat: {val: var_name(cat, val) for val in vals} for cat, vals in categories.items()}

    p = Problem()

    # Add variables
    for cat, vals in categories.items():
        for val in vals:
            p.addVariable(var_map[cat][val], houses)

    # AllDifferent per category
    for cat, vals in categories.items():
        p.addConstraint(AllDifferentConstraint(), [var_map[cat][val] for val in vals])

    # Constraints based on clues:

    # 1. Alice is not in the fourth house.
    p.addConstraint(lambda a: a != 4, [var_map["Name"]["Alice"]])

    # 2. The root beer lover is the person who enjoys gardening.
    p.addConstraint(lambda rb, g: rb == g, [var_map["Drink"]["root beer"], var_map["Hobby"]["gardening"]])

    # 3. The person whose favorite color is green is the coffee drinker.
    p.addConstraint(lambda gr, cf: gr == cf, [var_map["Color"]["green"], var_map["Drink"]["coffee"]])

    # 4. The person whose favorite color is green is the person who loves the boquet of lilies.
    p.addConstraint(lambda gr, li: gr == li, [var_map["Color"]["green"], var_map["Flower"]["lilies"]])

    # 5. The person who loves blue is somewhere to the right of the person who loves a bouquet of daffodils.
    p.addConstraint(lambda bl, da: bl > da, [var_map["Color"]["blue"], var_map["Flower"]["daffodils"]])

    # 6. The person who loves cooking is the person who loves blue.
    p.addConstraint(lambda co, bl: co == bl, [var_map["Hobby"]["cooking"], var_map["Color"]["blue"]])

    # 7. Eric is directly left of the tea drinker.
    p.addConstraint(lambda e, t: t - e == 1, [var_map["Name"]["Eric"], var_map["Drink"]["tea"]])

    # 8. The one who only drinks water is Peter.
    p.addConstraint(lambda w, pz: w == pz, [var_map["Drink"]["water"], var_map["Name"]["Peter"]])

    # 9. Arnold is the photography enthusiast.
    p.addConstraint(lambda ar, ph: ar == ph, [var_map["Name"]["Arnold"], var_map["Hobby"]["photography"]])

    # 10. The person who loves white is the person who loves the rose bouquet.
    p.addConstraint(lambda wh, ro: wh == ro, [var_map["Color"]["white"], var_map["Flower"]["roses"]])

    # 11. There is one house between the person who loves a carnations arrangement and the person whose favorite color is red.
    p.addConstraint(lambda ca, re: abs(ca - re) == 2, [var_map["Flower"]["carnations"], var_map["Color"]["red"]])

    # 12. The person who loves cooking is somewhere to the left of the person who paints as a hobby.
    p.addConstraint(lambda co, pa: co < pa, [var_map["Hobby"]["cooking"], var_map["Hobby"]["painting"]])

    # 13. The one who only drinks water is in the third house.
    p.addConstraint(lambda w: w == 3, [var_map["Drink"]["water"]])

    # 14. The person who loves a carnations arrangement is the root beer lover.
    p.addConstraint(lambda ca, rb: ca == rb, [var_map["Flower"]["carnations"], var_map["Drink"]["root beer"]])

    # 15. The person who loves white is in the second house.
    p.addConstraint(lambda wh: wh == 2, [var_map["Color"]["white"]])

    solutions = p.getSolutions()

    if not solutions:
        raise RuntimeError("No solution found for the given puzzle constraints.")

    # Choose the first solution (should be unique)
    sol = solutions[0]

    # Invert mapping to get value at each house for each category
    house_rows = []
    for h in houses:
        # Find values for each category at house h
        row = {}
        for cat, vals in categories.items():
            for val in vals:
                if sol[var_map[cat][val]] == h:
                    row[cat] = val
                    break
        house_rows.append(row)

    output = {
        "solution": {
            "header": ["House", "Name", "Drink", "Color", "Flower", "Hobby"],
            "rows": []
        }
    }

    for idx, row in enumerate(house_rows, start=1):
        output["solution"]["rows"].append([
            str(idx),
            row["Name"],
            row["Drink"],
            row["Color"],
            row["Flower"],
            row["Hobby"]
        ])

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()