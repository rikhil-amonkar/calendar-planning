import json

# Ensure python-constraint is available
try:
    from constraint import Problem, AllDifferentConstraint
except ImportError:
    import sys, subprocess
    subprocess.check_call([sys.executable, "-m", "pip", "install", "python-constraint"])
    from constraint import Problem, AllDifferentConstraint

def safe(s):
    return s.replace(" ", "_").replace("-", "_")

def main():
    houses = [1, 2, 3, 4, 5]

    categories = {
        "Name": ["Bob", "Arnold", "Alice", "Peter", "Eric"],
        "Hobby": ["cooking", "gardening", "painting", "photography", "knitting"],
        "FavoriteSport": ["swimming", "tennis", "soccer", "baseball", "basketball"],
        "HouseStyle": ["ranch", "craftsman", "victorian", "modern", "colonial"],
        "Children": ["Timothy", "Samantha", "Bella", "Meredith", "Fred"],
        "Height": ["average", "very tall", "very short", "short", "tall"],
    }

    # Create problem
    problem = Problem()

    # Create variables for each value in each category
    var_names = {}
    for cat, values in categories.items():
        var_names[cat] = {}
        for val in values:
            vname = f"{cat}_{safe(val)}"
            var_names[cat][val] = vname
            problem.addVariable(vname, houses)

    # AllDifferent within each category
    for cat in categories:
        problem.addConstraint(AllDifferentConstraint(), list(var_names[cat].values()))

    # Helper to get variable names quickly
    V = var_names

    # Clues implementation:

    # 1. average height <-> child Meredith
    problem.addConstraint(lambda h, c: h == c, (V["Height"]["average"], V["Children"]["Meredith"]))

    # 2. tall is in the second house
    problem.addConstraint(lambda x: x == 2, (V["Height"]["tall"],))

    # 3. Peter is directly left of Victorian
    problem.addConstraint(lambda p, v: p + 1 == v, (V["Name"]["Peter"], V["HouseStyle"]["victorian"]))

    # 4. Alice is tall
    problem.addConstraint(lambda a, t: a == t, (V["Name"]["Alice"], V["Height"]["tall"]))

    # 5. baseball <-> very tall
    problem.addConstraint(lambda s, h: s == h, (V["FavoriteSport"]["baseball"], V["Height"]["very tall"]))

    # 6. Meredith and Timothy are next to each other
    problem.addConstraint(lambda m, t: abs(m - t) == 1, (V["Children"]["Meredith"], V["Children"]["Timothy"]))

    # 7. Bob paints
    problem.addConstraint(lambda b, p: b == p, (V["Name"]["Bob"], V["Hobby"]["painting"]))

    # 8. gardening is in second house
    problem.addConstraint(lambda g: g == 2, (V["Hobby"]["gardening"],))

    # 9. very short is to the right of Eric
    problem.addConstraint(lambda vs, e: vs > e, (V["Height"]["very short"], V["Name"]["Eric"]))

    # 10. tennis <-> Samantha
    problem.addConstraint(lambda spt, ch: spt == ch, (V["FavoriteSport"]["tennis"], V["Children"]["Samantha"]))

    # 11. soccer not in the first house
    problem.addConstraint(lambda s: s != 1, (V["FavoriteSport"]["soccer"],))

    # 12. Samantha <-> modern
    problem.addConstraint(lambda ch, st: ch == st, (V["Children"]["Samantha"], V["HouseStyle"]["modern"]))

    # 13. craftsman <-> average
    problem.addConstraint(lambda st, h: st == h, (V["HouseStyle"]["craftsman"], V["Height"]["average"]))

    # 14. Fred <-> Victorian
    problem.addConstraint(lambda ch, st: ch == st, (V["Children"]["Fred"], V["HouseStyle"]["victorian"]))

    # 15. short <-> basketball
    problem.addConstraint(lambda h, s: h == s, (V["Height"]["short"], V["FavoriteSport"]["basketball"]))

    # 16. Peter very tall
    problem.addConstraint(lambda n, h: n == h, (V["Name"]["Peter"], V["Height"]["very tall"]))

    # 17. ranch left of cooking
    problem.addConstraint(lambda r, c: r < c, (V["HouseStyle"]["ranch"], V["Hobby"]["cooking"]))

    # 18. knitting and gardening adjacent
    problem.addConstraint(lambda k, g: abs(k - g) == 1, (V["Hobby"]["knitting"], V["Hobby"]["gardening"]))

    # 19. modern <-> cooking
    problem.addConstraint(lambda st, hb: st == hb, (V["HouseStyle"]["modern"], V["Hobby"]["cooking"]))

    # 20. Victorian is in the fifth house
    problem.addConstraint(lambda v: v == 5, (V["HouseStyle"]["victorian"],))

    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No solution found.")

    # Assuming unique solution; take the first
    sol = solutions[0]

    # Build inverse mapping for each house
    header = ["House", "Name", "Hobby", "FavoriteSport", "HouseStyle", "Children", "Height"]
    rows = []
    for h in houses:
        # Find values per category at house h
        row = [str(h)]
        # Name
        name_val = next(val for val in categories["Name"] if sol[V["Name"][val]] == h)
        row.append(name_val)
        # Hobby
        hobby_val = next(val for val in categories["Hobby"] if sol[V["Hobby"][val]] == h)
        row.append(hobby_val)
        # FavoriteSport
        sport_val = next(val for val in categories["FavoriteSport"] if sol[V["FavoriteSport"][val]] == h)
        row.append(sport_val)
        # HouseStyle
        style_val = next(val for val in categories["HouseStyle"] if sol[V["HouseStyle"][val]] == h)
        row.append(style_val)
        # Children
        child_val = next(val for val in categories["Children"] if sol[V["Children"][val]] == h)
        row.append(child_val)
        # Height
        height_val = next(val for val in categories["Height"] if sol[V["Height"][val]] == h)
        row.append(height_val)

        rows.append(row)

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(output))

if __name__ == "__main__":
    main()