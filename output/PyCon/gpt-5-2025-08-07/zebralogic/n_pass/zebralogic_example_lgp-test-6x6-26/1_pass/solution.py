import json
from constraint import Problem, AllDifferentConstraint

def main():
    houses = range(1, 7)

    names = ["Peter", "Carol", "Eric", "Alice", "Bob", "Arnold"]
    phones = ["huawei p50", "google pixel 6", "xiaomi mi 11", "iphone 13", "samsung galaxy s21", "oneplus 9"]
    cigars = ["dunhill", "pall mall", "blends", "blue master", "prince", "yellow monster"]
    flowers = ["daffodils", "carnations", "roses", "tulips", "lilies", "iris"]
    colors = ["yellow", "red", "green", "blue", "white", "purple"]
    sports = ["soccer", "tennis", "basketball", "volleyball", "swimming", "baseball"]

    problem = Problem()

    # Create variables with prefixed names to avoid collisions
    var_names = {n: f"Name:{n}" for n in names}
    var_phones = {p: f"Phone:{p}" for p in phones}
    var_cigars = {c: f"Cigar:{c}" for c in cigars}
    var_flowers = {f: f"Flower:{f}" for f in flowers}
    var_colors = {c: f"Color:{c}" for c in colors}
    var_sports = {s: f"Sport:{s}" for s in sports}

    # Add variables to the problem
    for v in var_names.values():
        problem.addVariable(v, houses)
    for v in var_phones.values():
        problem.addVariable(v, houses)
    for v in var_cigars.values():
        problem.addVariable(v, houses)
    for v in var_flowers.values():
        problem.addVariable(v, houses)
    for v in var_colors.values():
        problem.addVariable(v, houses)
    for v in var_sports.values():
        problem.addVariable(v, houses)

    # AllDifferent constraints per category
    problem.addConstraint(AllDifferentConstraint(), list(var_names.values()))
    problem.addConstraint(AllDifferentConstraint(), list(var_phones.values()))
    problem.addConstraint(AllDifferentConstraint(), list(var_cigars.values()))
    problem.addConstraint(AllDifferentConstraint(), list(var_flowers.values()))
    problem.addConstraint(AllDifferentConstraint(), list(var_colors.values()))
    problem.addConstraint(AllDifferentConstraint(), list(var_sports.values()))

    # Clues:

    # 1. OnePlus 9 is in the second house.
    problem.addConstraint(lambda x: x == 2, [var_phones["oneplus 9"]])

    # 2. Xiaomi Mi 11 is somewhere to the left of Huawei P50.
    problem.addConstraint(lambda x, h: x < h, [var_phones["xiaomi mi 11"], var_phones["huawei p50"]])

    # 3. Carol is the person who loves a carnations arrangement.
    problem.addConstraint(lambda n, f: n == f, [var_names["Carol"], var_flowers["carnations"]])

    # 4. Purple directly left of Pall Mall.
    problem.addConstraint(lambda purple, pall: purple + 1 == pall, [var_colors["purple"], var_cigars["pall mall"]])

    # 5. Green is Blue Master.
    problem.addConstraint(lambda g, bm: g == bm, [var_colors["green"], var_cigars["blue master"]])

    # 6. Yellow and Blue are next to each other.
    problem.addConstraint(lambda y, b: abs(y - b) == 1, [var_colors["yellow"], var_colors["blue"]])

    # 7. Eric is to the right of Samsung Galaxy S21.
    problem.addConstraint(lambda e, s: e > s, [var_names["Eric"], var_phones["samsung galaxy s21"]])

    # 8. Two houses between Carol and daffodils.
    problem.addConstraint(lambda c, d: abs(c - d) == 3, [var_names["Carol"], var_flowers["daffodils"]])

    # 9. Prince smoker loves basketball.
    problem.addConstraint(lambda p, b: p == b, [var_cigars["prince"], var_sports["basketball"]])

    # 10. Dunhill smoker loves volleyball.
    problem.addConstraint(lambda d, v: d == v, [var_cigars["dunhill"], var_sports["volleyball"]])

    # 11. Swimming is Google Pixel 6.
    problem.addConstraint(lambda sw, gp: sw == gp, [var_sports["swimming"], var_phones["google pixel 6"]])

    # 12. Huawei P50 directly left of White.
    problem.addConstraint(lambda h, w: h + 1 == w, [var_phones["huawei p50"], var_colors["white"]])

    # 13. OnePlus 9 and roses are next to each other.
    problem.addConstraint(lambda op, r: abs(op - r) == 1, [var_phones["oneplus 9"], var_flowers["roses"]])

    # 14. Iris is to the left of Eric.
    problem.addConstraint(lambda i, e: i < e, [var_flowers["iris"], var_names["Eric"]])

    # 15. Dunhill smoker is Peter.
    problem.addConstraint(lambda d, p: d == p, [var_cigars["dunhill"], var_names["Peter"]])

    # 16. Blue is Peter.
    problem.addConstraint(lambda b, p: b == p, [var_colors["blue"], var_names["Peter"]])

    # 17. Tulips is Bob.
    problem.addConstraint(lambda t, b: t == b, [var_flowers["tulips"], var_names["Bob"]])

    # 18. Alice is in the first house.
    problem.addConstraint(lambda a: a == 1, [var_names["Alice"]])

    # 19. Baseball directly left of Blue Master.
    problem.addConstraint(lambda base, bm: base + 1 == bm, [var_sports["baseball"], var_cigars["blue master"]])

    # 20. Google Pixel 6 is to the right of Blends.
    problem.addConstraint(lambda gp, bl: gp > bl, [var_phones["google pixel 6"], var_cigars["blends"]])

    # 21. Soccer is Carol.
    problem.addConstraint(lambda s, c: s == c, [var_sports["soccer"], var_names["Carol"]])

    # 22. Carnations directly left of Blends.
    problem.addConstraint(lambda car, bl: car + 1 == bl, [var_flowers["carnations"], var_cigars["blends"]])

    # 23. Eric is Blends.
    problem.addConstraint(lambda e, bl: e == bl, [var_names["Eric"], var_cigars["blends"]])

    # 24. Volleyball is iPhone 13.
    problem.addConstraint(lambda v, ip: v == ip, [var_sports["volleyball"], var_phones["iphone 13"]])

    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No solution found")

    sol = solutions[0]

    def find_value_at_position(category_items, var_map, pos):
        for item in category_items:
            if sol[var_map[item]] == pos:
                return item
        return None

    header = ["House", "Name", "PhoneModel", "Cigar", "Flower", "Color", "FavoriteSport"]
    rows = []
    for pos in range(1, 7):
        row = [
            str(pos),
            find_value_at_position(names, var_names, pos),
            find_value_at_position(phones, var_phones, pos),
            find_value_at_position(cigars, var_cigars, pos),
            find_value_at_position(flowers, var_flowers, pos),
            find_value_at_position(colors, var_colors, pos),
            find_value_at_position(sports, var_sports, pos),
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