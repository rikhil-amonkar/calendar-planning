import json
from constraint import Problem, AllDifferentConstraint

def main():
    houses = [1, 2, 3, 4, 5]

    Names = ["Peter", "Arnold", "Eric", "Bob", "Alice"]
    Heights = ["average", "very tall", "very short", "short", "tall"]
    Cigars = ["prince", "dunhill", "blends", "pall mall", "blue master"]
    Smoothies = ["lime", "cherry", "dragonfruit", "watermelon", "desert"]
    Phones = ["oneplus 9", "samsung galaxy s21", "iphone 13", "huawei p50", "google pixel 6"]

    categories = {
        "Name": Names,
        "Height": Heights,
        "Cigar": Cigars,
        "Smoothie": Smoothies,
        "PhoneModel": Phones,
    }

    # Helper to create variable names
    def var_name(category, value):
        return f"{category}_{value}".replace(" ", "_")

    # Build variables for the problem
    problem = Problem()
    vars_map = {cat: {} for cat in categories}
    for cat, values in categories.items():
        for val in values:
            vname = var_name(cat, val)
            vars_map[cat][val] = vname
            problem.addVariable(vname, houses)

    # All-different within each category
    for cat, values in categories.items():
        problem.addConstraint(AllDifferentConstraint(), [vars_map[cat][v] for v in values])

    # Convenience accessors
    def V(cat, val):
        return vars_map[cat][val]

    # Constraints from clues:

    # 1. The Prince smoker is the Desert smoothie lover.
    problem.addConstraint(lambda a, b: a == b, (V("Cigar", "prince"), V("Smoothie", "desert")))

    # 2. There is one house between Eric and Alice. (difference of 2)
    problem.addConstraint(lambda a, b: abs(a - b) == 2, (V("Name", "Eric"), V("Name", "Alice")))

    # 3. The person who is short is the person who smokes many unique blends.
    problem.addConstraint(lambda a, b: a == b, (V("Height", "short"), V("Cigar", "blends")))

    # 4. The person who uses an iPhone 13 is directly left of the person who smokes Blue Master.
    problem.addConstraint(lambda a, b: a + 1 == b, (V("PhoneModel", "iphone 13"), V("Cigar", "blue master")))

    # 5. The person who has an average height is the Dunhill smoker.
    problem.addConstraint(lambda a, b: a == b, (V("Height", "average"), V("Cigar", "dunhill")))

    # 6. Eric is the person who is very tall.
    problem.addConstraint(lambda a, b: a == b, (V("Name", "Eric"), V("Height", "very tall")))

    # 7. Arnold is directly left of the person who uses a Huawei P50.
    problem.addConstraint(lambda a, b: a + 1 == b, (V("Name", "Arnold"), V("PhoneModel", "huawei p50")))

    # 8. Bob is not in the fourth house.
    problem.addConstraint(lambda a: a != 4, (V("Name", "Bob"),))

    # 9. Eric is directly left of the person who likes Cherry smoothies.
    problem.addConstraint(lambda a, b: a + 1 == b, (V("Name", "Eric"), V("Smoothie", "cherry")))

    # 10. Bob is the Dunhill smoker.
    problem.addConstraint(lambda a, b: a == b, (V("Name", "Bob"), V("Cigar", "dunhill")))

    # 11. The Dragonfruit smoothie lover is Bob.
    problem.addConstraint(lambda a, b: a == b, (V("Smoothie", "dragonfruit"), V("Name", "Bob")))

    # 12. The person who uses an iPhone 13 and the person who uses a OnePlus 9 are next to each other.
    problem.addConstraint(lambda a, b: abs(a - b) == 1, (V("PhoneModel", "iphone 13"), V("PhoneModel", "oneplus 9")))

    # 13. The person who uses a Samsung Galaxy S21 is the person who is short.
    problem.addConstraint(lambda a, b: a == b, (V("PhoneModel", "samsung galaxy s21"), V("Height", "short")))

    # 14. There are two houses between the person who is very tall and the Dragonfruit smoothie lover. (difference of 3)
    problem.addConstraint(lambda a, b: abs(a - b) == 3, (V("Height", "very tall"), V("Smoothie", "dragonfruit")))

    # 15. The person who uses an iPhone 13 is Eric.
    problem.addConstraint(lambda a, b: a == b, (V("PhoneModel", "iphone 13"), V("Name", "Eric")))

    # 16. The Desert smoothie lover is somewhere to the left of the person who drinks Lime smoothies.
    problem.addConstraint(lambda a, b: a < b, (V("Smoothie", "desert"), V("Smoothie", "lime")))

    # 17. Arnold and the person who is very short are next to each other.
    problem.addConstraint(lambda a, b: abs(a - b) == 1, (V("Name", "Arnold"), V("Height", "very short")))

    solution = problem.getSolution()
    if solution is None:
        raise RuntimeError("No solution found")

    # Build rows per house
    header = ["House", "Name", "Height", "Cigar", "Smoothie", "PhoneModel"]
    rows = []
    for house in houses:
        # Find the value for each category that matches this house
        def value_for(cat):
            for val in categories[cat]:
                if solution[V(cat, val)] == house:
                    return val
            return None

        row = [
            str(house),
            value_for("Name"),
            value_for("Height"),
            value_for("Cigar"),
            value_for("Smoothie"),
            value_for("PhoneModel"),
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