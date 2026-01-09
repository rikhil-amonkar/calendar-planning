import json
from constraint import Problem, AllDifferentConstraint

def main():
    problem = Problem()

    houses = range(1, 7)

    Names = ["Arnold", "Carol", "Peter", "Eric", "Bob", "Alice"]
    HouseStyles = ["ranch", "colonial", "modern", "craftsman", "mediterranean", "victorian"]
    Foods = ["pizza", "stew", "spaghetti", "grilled cheese", "stir fry", "soup"]
    Vacations = ["cultural", "cruise", "mountain", "camping", "city", "beach"]
    Heights = ["average", "very tall", "very short", "short", "tall", "super tall"]
    Cigars = ["yellow monster", "prince", "dunhill", "pall mall", "blue master", "blends"]

    # Helper to create variable names
    def var_name(category, item):
        return f"{category}:{item}"

    # Create variables
    var_maps = {}
    for category, items in [
        ("Name", Names),
        ("HouseStyle", HouseStyles),
        ("Food", Foods),
        ("Vacation", Vacations),
        ("Height", Heights),
        ("Cigar", Cigars),
    ]:
        var_maps[category] = {}
        for item in items:
            v = var_name(category, item)
            var_maps[category][item] = v
            problem.addVariable(v, houses)
        # All different within category
        problem.addConstraint(AllDifferentConstraint(), [var_maps[category][item] for item in items])

    Name = var_maps["Name"]
    HouseStyle = var_maps["HouseStyle"]
    Food = var_maps["Food"]
    Vacation = var_maps["Vacation"]
    Height = var_maps["Height"]
    Cigar = var_maps["Cigar"]

    # Constraints based on clues

    # 1. Alice is in the fifth house.
    problem.addConstraint(lambda a: a == 5, (Name["Alice"],))

    # 2. Stir fry = colonial
    problem.addConstraint(lambda f, h: f == h, (Food["stir fry"], HouseStyle["colonial"]))

    # 3. Alice loves spaghetti (interpreting "loves the spaghetti eater" as loves spaghetti)
    # and 14 combined later: spaghetti eater resides in Victorian
    problem.addConstraint(lambda a, s, v: a == s == v,
                          (Name["Alice"], Food["spaghetti"], HouseStyle["victorian"]))

    # 4. Arnold loves stew.
    problem.addConstraint(lambda n, f: n == f, (Name["Arnold"], Food["stew"]))

    # 5. One house between average and Peter.
    problem.addConstraint(lambda avg, p: abs(avg - p) == 2, (Height["average"], Name["Peter"]))

    # 6. Craftsman not in third.
    problem.addConstraint(lambda c: c != 3, (HouseStyle["craftsman"],))

    # 7. Average = stir fry.
    problem.addConstraint(lambda h, f: h == f, (Height["average"], Food["stir fry"]))

    # 8. Beach = ranch.
    problem.addConstraint(lambda v, h: v == h, (Vacation["beach"], HouseStyle["ranch"]))

    # 9. Eric is in the fourth house.
    problem.addConstraint(lambda e: e == 4, (Name["Eric"],))

    # 10. One house between colonial and camping.
    problem.addConstraint(lambda col, camp: abs(col - camp) == 2, (HouseStyle["colonial"], Vacation["camping"]))

    # 11. Mountain = Yellow Monster.
    problem.addConstraint(lambda v, c: v == c, (Vacation["mountain"], Cigar["yellow monster"]))

    # 12. Mountain = very tall.
    problem.addConstraint(lambda v, h: v == h, (Vacation["mountain"], Height["very tall"]))

    # 13. Mountain and Dunhill are next to each other.
    problem.addConstraint(lambda m, d: abs(m - d) == 1, (Vacation["mountain"], Cigar["dunhill"]))

    # 14. (handled with 3) The spaghetti eater resides in a Victorian house. Already linked above.

    # 15. Tall = beach.
    problem.addConstraint(lambda ht, vac: ht == vac, (Height["tall"], Vacation["beach"]))

    # 16. Tall somewhere to the left of Victorian.
    problem.addConstraint(lambda tall, vict: tall < vict, (Height["tall"], HouseStyle["victorian"]))

    # 17. Stir fry directly left of Bob.
    problem.addConstraint(lambda sf, bob: sf + 1 == bob, (Food["stir fry"], Name["Bob"]))

    # 18. Modern somewhere to the left of Alice.
    problem.addConstraint(lambda mod, alice: mod < alice, (HouseStyle["modern"], Name["Alice"]))

    # 19. Craftsman left of short.
    problem.addConstraint(lambda cr, sh: cr < sh, (HouseStyle["craftsman"], Height["short"]))

    # 20. Stir fry left of Prince.
    problem.addConstraint(lambda sf, pr: sf < pr, (Food["stir fry"], Cigar["prince"]))

    # 21. Two houses between grilled cheese and super tall.
    problem.addConstraint(lambda gc, st: abs(gc - st) == 3, (Food["grilled cheese"], Height["super tall"]))

    # 22. Ranch = Blue Master.
    problem.addConstraint(lambda hs, cg: hs == cg, (HouseStyle["ranch"], Cigar["blue master"]))

    # 23. Blends directly left of Blue Master.
    problem.addConstraint(lambda bl, bm: bl + 1 == bm, (Cigar["blends"], Cigar["blue master"]))

    # 24. Cultural = pizza.
    problem.addConstraint(lambda cul, piz: cul == piz, (Vacation["cultural"], Food["pizza"]))

    # 25. Pizza left of cruise.
    problem.addConstraint(lambda piz, cru: piz < cru, (Food["pizza"], Vacation["cruise"]))

    solutions = problem.getSolutions()

    if not solutions:
        raise RuntimeError("No solution found")

    sol = solutions[0]

    # Build reverse lookup for each category
    def invert(category_items):
        inverse = {}
        for item in category_items:
            pos = sol[var_maps[category][item]]
            inverse[pos] = item
        return inverse

    category = "Name"
    name_at = invert(Names)
    category = "HouseStyle"
    style_at = invert(HouseStyles)
    category = "Food"
    food_at = invert(Foods)
    category = "Vacation"
    vacation_at = invert(Vacations)
    category = "Height"
    height_at = invert(Heights)
    category = "Cigar"
    cigar_at = invert(Cigars)

    header = ["House", "Name", "HouseStyle", "Food", "Vacation", "Height", "Cigar"]
    rows = []
    for h in range(1, 7):
        row = [
            str(h),
            name_at[h],
            style_at[h],
            food_at[h],
            vacation_at[h],
            height_at[h],
            cigar_at[h],
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()