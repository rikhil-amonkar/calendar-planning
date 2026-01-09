import json

# Ensure python-constraint is available
try:
    from constraint import Problem, AllDifferentConstraint
except ImportError:
    import sys
    import subprocess
    subprocess.check_call([sys.executable, "-m", "pip", "install", "python-constraint"])
    from constraint import Problem, AllDifferentConstraint


def main():
    problem = Problem()

    houses = [1, 2, 3, 4, 5]

    # Attributes
    Names = ["Eric", "Peter", "Arnold", "Bob", "Alice"]
    HouseStyles = ["modern", "craftsman", "ranch", "victorian", "colonial"]
    Mothers = ["Penny", "Kailyn", "Holly", "Janelle", "Aniya"]
    Phones = ["oneplus 9", "google pixel 6", "huawei p50", "iphone 13", "samsung galaxy s21"]
    Drinks = ["coffee", "water", "root beer", "tea", "milk"]
    Animals = ["fish", "dog", "horse", "bird", "cat"]

    # Add variables
    for v in Names + HouseStyles + Mothers + Phones + Drinks + Animals:
        problem.addVariable(v, houses)

    # AllDifferent per category
    problem.addConstraint(AllDifferentConstraint(), Names)
    problem.addConstraint(AllDifferentConstraint(), HouseStyles)
    problem.addConstraint(AllDifferentConstraint(), Mothers)
    problem.addConstraint(AllDifferentConstraint(), Phones)
    problem.addConstraint(AllDifferentConstraint(), Drinks)
    problem.addConstraint(AllDifferentConstraint(), Animals)

    # Clues:
    # 1. The person who uses a Google Pixel 6 is not in the first house.
    problem.addConstraint(lambda x: x != 1, ("google pixel 6",))

    # 2. The one who only drinks water is Alice.
    problem.addConstraint(lambda a, w: a == w, ("Alice", "water"))

    # 3. The person living in a colonial-style house is somewhere to the right of the person who uses a Huawei P50.
    problem.addConstraint(lambda c, h: c > h, ("colonial", "huawei p50"))

    # 4. The person who keeps horses is the person who uses a OnePlus 9.
    problem.addConstraint(lambda animal, phone: animal == phone, ("horse", "oneplus 9"))

    # 5. The person in a ranch-style home is The person whose mother's name is Kailyn.
    problem.addConstraint(lambda style, mom: style == mom, ("ranch", "Kailyn"))

    # 6. The root beer lover is the cat lover.
    problem.addConstraint(lambda drink, animal: drink == animal, ("root beer", "cat"))

    # 7. The person living in a colonial-style house is not in the fourth house.
    problem.addConstraint(lambda c: c != 4, ("colonial",))

    # 8. The bird keeper is in the fourth house.
    problem.addConstraint(lambda b: b == 4, ("bird",))

    # 9. The tea drinker is Bob.
    problem.addConstraint(lambda tea_pos, bob_pos: tea_pos == bob_pos, ("tea", "Bob"))

    # 10. The tea drinker is somewhere to the right of The person whose mother's name is Kailyn.
    problem.addConstraint(lambda tea_pos, mom_pos: tea_pos > mom_pos, ("tea", "Kailyn"))

    # 11. The root beer lover is somewhere to the left of The person whose mother's name is Kailyn.
    problem.addConstraint(lambda rb_pos, mom_pos: rb_pos < mom_pos, ("root beer", "Kailyn"))

    # 12. The person who keeps horses is the person in a modern-style house.
    problem.addConstraint(lambda animal, style: animal == style, ("horse", "modern"))

    # 13. The person who uses an iPhone 13 is the person who likes milk.
    problem.addConstraint(lambda phone, drink: phone == drink, ("iphone 13", "milk"))

    # 14. The dog owner is the person who likes milk.
    problem.addConstraint(lambda animal, drink: animal == drink, ("dog", "milk"))

    # 15. The person who uses a Google Pixel 6 is the person in a Craftsman-style house.
    problem.addConstraint(lambda phone, style: phone == style, ("google pixel 6", "craftsman"))

    # 16. Eric is not in the second house.
    problem.addConstraint(lambda x: x != 2, ("Eric",))

    # 17. The tea drinker is in the fourth house.
    problem.addConstraint(lambda t: t == 4, ("tea",))

    # 18. The person who keeps horses is in the third house.
    problem.addConstraint(lambda h: h == 3, ("horse",))

    # 19. The person in a modern-style house is The person whose mother's name is Penny.
    problem.addConstraint(lambda style, mom: style == mom, ("modern", "Penny"))

    # 20. The root beer lover is Peter.
    problem.addConstraint(lambda drink, name: drink == name, ("root beer", "Peter"))

    # 21. The person whose mother's name is Aniya is not in the fourth house.
    problem.addConstraint(lambda a: a != 4, ("Aniya",))

    # 22. The person whose mother's name is Janelle is the one who only drinks water.
    problem.addConstraint(lambda mom, drink: mom == drink, ("Janelle", "water"))

    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No solution found for the puzzle.")
    sol = solutions[0]

    # Build output rows per house 1..5
    header = ["House", "Name", "HouseStyle", "Mother", "PhoneModel", "Drink", "Animal"]
    rows = []
    for h in houses:
        name = next(v for v in Names if sol[v] == h)
        style = next(v for v in HouseStyles if sol[v] == h)
        mother = next(v for v in Mothers if sol[v] == h)
        phone = next(v for v in Phones if sol[v] == h)
        drink = next(v for v in Drinks if sol[v] == h)
        animal = next(v for v in Animals if sol[v] == h)
        rows.append([str(h), name, style, mother, phone, drink, animal])

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(output))


if __name__ == "__main__":
    main()