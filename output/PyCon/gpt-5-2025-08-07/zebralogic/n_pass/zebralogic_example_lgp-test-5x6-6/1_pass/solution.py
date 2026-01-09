import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    houses = range(1, 6)

    Names = ["Arnold", "Eric", "Alice", "Bob", "Peter"]
    Vacations = ["mountain", "city", "cruise", "beach", "camping"]
    Educations = ["doctorate", "high school", "bachelor", "associate", "master"]
    Colors = ["blue", "red", "white", "yellow", "green"]
    Phones = ["google pixel 6", "iphone 13", "oneplus 9", "huawei p50", "samsung galaxy s21"]
    Foods = ["grilled cheese", "stir fry", "pizza", "spaghetti", "stew"]

    problem = Problem()

    # Add variables for each attribute value with domain 1..5 (house positions)
    for category in [Names, Vacations, Educations, Colors, Phones, Foods]:
        for item in category:
            problem.addVariable(item, houses)

    # AllDifferent constraints within each category
    problem.addConstraint(AllDifferentConstraint(), Names)
    problem.addConstraint(AllDifferentConstraint(), Vacations)
    problem.addConstraint(AllDifferentConstraint(), Educations)
    problem.addConstraint(AllDifferentConstraint(), Colors)
    problem.addConstraint(AllDifferentConstraint(), Phones)
    problem.addConstraint(AllDifferentConstraint(), Foods)

    # Clues as constraints

    # 1. Stew is not in the first house.
    problem.addConstraint(lambda s: s != 1, ["stew"])

    # 2. Two houses between stir fry and associate.
    problem.addConstraint(lambda sf, assoc: abs(sf - assoc) == 3, ["stir fry", "associate"])

    # 3. Mountain retreats is the person with a bachelor's degree.
    problem.addConstraint(lambda m, b: m == b, ["mountain", "bachelor"])

    # 4. Doctorate is somewhere to the right of Bob.
    problem.addConstraint(lambda doc, bob: doc > bob, ["doctorate", "Bob"])

    # 5. Samsung Galaxy S21 is in the third house.
    problem.addConstraint(lambda s21: s21 == 3, ["samsung galaxy s21"])

    # 6. Eric is the person with a doctorate.
    problem.addConstraint(lambda eric, doc: eric == doc, ["Eric", "doctorate"])

    # 7. Doctorate is in the third house.
    problem.addConstraint(lambda doc: doc == 3, ["doctorate"])

    # 8. Stir fry is the person with a bachelor's degree.
    problem.addConstraint(lambda sf, b: sf == b, ["stir fry", "bachelor"])

    # 9. Doctorate is the person who is a pizza lover.
    problem.addConstraint(lambda doc, piz: doc == piz, ["doctorate", "pizza"])

    # 10. Green is somewhere to the right of Peter.
    problem.addConstraint(lambda green, peter: green > peter, ["green", "Peter"])

    # 11. Camping is the person who uses an iPhone 13.
    problem.addConstraint(lambda camp, ip: camp == ip, ["camping", "iphone 13"])

    # 12. Cruises is Alice.
    problem.addConstraint(lambda cruise, alice: cruise == alice, ["cruise", "Alice"])

    # 13. One house between high school and Samsung Galaxy S21 (which is house 3).
    problem.addConstraint(lambda hs: abs(hs - 3) == 2, ["high school"])

    # 14. Google Pixel 6 is Arnold.
    problem.addConstraint(lambda gp6, arnold: gp6 == arnold, ["google pixel 6", "Arnold"])

    # 15. OnePlus 9 is somewhere to the right of Huawei P50.
    problem.addConstraint(lambda op, hw: op > hw, ["oneplus 9", "huawei p50"])

    # 16. Arnold loves eating grilled cheese.
    problem.addConstraint(lambda arnold, gc: arnold == gc, ["Arnold", "grilled cheese"])

    # 17. Grilled cheese is not in the fourth house.
    problem.addConstraint(lambda gc: gc != 4, ["grilled cheese"])

    # 18. Two houses between bachelor's degree and red.
    problem.addConstraint(lambda b, r: abs(b - r) == 3, ["bachelor", "red"])

    # 19. Beach is to the right of city.
    problem.addConstraint(lambda beach, city: beach > city, ["beach", "city"])

    # 20. Green is not in the second house.
    problem.addConstraint(lambda green: green != 2, ["green"])

    # 21. Blue is somewhere to the right of Peter.
    problem.addConstraint(lambda blue, peter: blue > peter, ["blue", "Peter"])

    # 22. One house between camping and yellow.
    problem.addConstraint(lambda camp, y: abs(camp - y) == 2, ["camping", "yellow"])

    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No solution found")

    # Select the first solution (should be unique)
    sol = solutions[0]

    # Build output rows per house 1..5
    header = ["House", "Name", "Vacation", "Education", "Color", "PhoneModel", "Food"]
    rows = []
    for h in range(1, 6):
        name = next(n for n in Names if sol[n] == h)
        vacation = next(v for v in Vacations if sol[v] == h)
        education = next(e for e in Educations if sol[e] == h)
        color = next(c for c in Colors if sol[c] == h)
        phone = next(p for p in Phones if sol[p] == h)
        food = next(f for f in Foods if sol[f] == h)
        rows.append([str(h), name, vacation, education, color, phone, food])

    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()