import json
from constraint import Problem, AllDifferentConstraint

def main():
    houses = range(1, 6)

    # Categories and values
    names = ["Eric", "Peter", "Arnold", "Alice", "Bob"]
    foods = ["stir fry", "spaghetti", "stew", "grilled cheese", "pizza"]
    cars = ["ford f150", "tesla model 3", "bmw 3 series", "toyota camry", "honda civic"]
    phones = ["iphone 13", "google pixel 6", "samsung galaxy s21", "oneplus 9", "huawei p50"]
    occupations = ["teacher", "lawyer", "doctor", "artist", "engineer"]
    drinks = ["tea", "milk", "water", "root beer", "coffee"]

    def var(category, value):
        return f"{category}:{value}"

    problem = Problem()

    # Add variables for each attribute, domain 1..5 (house positions)
    for n in names:
        problem.addVariable(var("Name", n), houses)
    for f in foods:
        problem.addVariable(var("Food", f), houses)
    for c in cars:
        problem.addVariable(var("Car", c), houses)
    for p in phones:
        problem.addVariable(var("Phone", p), houses)
    for o in occupations:
        problem.addVariable(var("Occupation", o), houses)
    for d in drinks:
        problem.addVariable(var("Drink", d), houses)

    # All different constraints within each category
    problem.addConstraint(AllDifferentConstraint(), [var("Name", n) for n in names])
    problem.addConstraint(AllDifferentConstraint(), [var("Food", f) for f in foods])
    problem.addConstraint(AllDifferentConstraint(), [var("Car", c) for c in cars])
    problem.addConstraint(AllDifferentConstraint(), [var("Phone", p) for p in phones])
    problem.addConstraint(AllDifferentConstraint(), [var("Occupation", o) for o in occupations])
    problem.addConstraint(AllDifferentConstraint(), [var("Drink", d) for d in drinks])

    # Clues implementation

    # 1. The root beer lover is the person who owns a Honda Civic.
    problem.addConstraint(lambda rb, hc: rb == hc,
                          [var("Drink", "root beer"), var("Car", "honda civic")])

    # 2. Milk is directly left of grilled cheese.
    problem.addConstraint(lambda milk, gc: milk == gc - 1,
                          [var("Drink", "milk"), var("Food", "grilled cheese")])

    # 3. Alice uses a Samsung Galaxy S21.
    problem.addConstraint(lambda a, s21: a == s21,
                          [var("Name", "Alice"), var("Phone", "samsung galaxy s21")])

    # 4. Alice loves stir fry.
    problem.addConstraint(lambda a, sf: a == sf,
                          [var("Name", "Alice"), var("Food", "stir fry")])

    # 5. Tea drinker is not in the fifth house.
    problem.addConstraint(lambda t: t != 5, [var("Drink", "tea")])

    # 6. BMW 3 Series is somewhere to the left of tea drinker.
    problem.addConstraint(lambda bmw, tea: bmw < tea,
                          [var("Car", "bmw 3 series"), var("Drink", "tea")])

    # 7. Doctor is Arnold.
    problem.addConstraint(lambda doc, arn: doc == arn,
                          [var("Occupation", "doctor"), var("Name", "Arnold")])

    # 8. iPhone 13 user is the coffee drinker.
    problem.addConstraint(lambda ip13, coffee: ip13 == coffee,
                          [var("Phone", "iphone 13"), var("Drink", "coffee")])

    # 9. Engineer is the BMW 3 Series owner.
    problem.addConstraint(lambda eng, bmw: eng == bmw,
                          [var("Occupation", "engineer"), var("Car", "bmw 3 series")])

    # 10. Stew lover uses an iPhone 13.
    problem.addConstraint(lambda stew, ip13: stew == ip13,
                          [var("Food", "stew"), var("Phone", "iphone 13")])

    # 11. Doctor is directly left of OnePlus 9 user.
    problem.addConstraint(lambda doc, op9: doc == op9 - 1,
                          [var("Occupation", "doctor"), var("Phone", "oneplus 9")])

    # 12. Honda Civic owner is directly left of the spaghetti eater.
    problem.addConstraint(lambda hc, sp: hc == sp - 1,
                          [var("Car", "honda civic"), var("Food", "spaghetti")])

    # 13. Google Pixel 6 user is the tea drinker.
    problem.addConstraint(lambda px6, tea: px6 == tea,
                          [var("Phone", "google pixel 6"), var("Drink", "tea")])

    # 14. Alice is an artist.
    problem.addConstraint(lambda a, art: a == art,
                          [var("Name", "Alice"), var("Occupation", "artist")])

    # 15. One house between Alice and the Ford F-150 owner.
    problem.addConstraint(lambda a, f150: abs(a - f150) == 2,
                          [var("Name", "Alice"), var("Car", "ford f150")])

    # 16. Arnold owns a Toyota Camry.
    problem.addConstraint(lambda arn, cam: arn == cam,
                          [var("Name", "Arnold"), var("Car", "toyota camry")])

    # 17. Eric is in the fourth house.
    problem.addConstraint(lambda e: e == 4, [var("Name", "Eric")])

    # 18. OnePlus 9 user is a lawyer.
    problem.addConstraint(lambda op9, law: op9 == law,
                          [var("Phone", "oneplus 9"), var("Occupation", "lawyer")])

    # 19. Grilled cheese lover is Peter.
    problem.addConstraint(lambda gc, peter: gc == peter,
                          [var("Food", "grilled cheese"), var("Name", "Peter")])

    solution = problem.getSolution()
    if solution is None:
        # Fallback empty JSON if no solution (should not happen for a valid puzzle)
        output = {
            "solution": {
                "header": ["House", "Name", "Food", "CarModel", "PhoneModel", "Occupation", "Drink"],
                "rows": []
            }
        }
        print(json.dumps(output, indent=2))
        return

    def value_at(sol, category, values, house):
        for v in values:
            if sol[var(category, v)] == house:
                return v
        return None

    header = ["House", "Name", "Food", "CarModel", "PhoneModel", "Occupation", "Drink"]
    rows = []
    for h in range(1, 6):
        rows.append([
            str(h),
            value_at(solution, "Name", names, h),
            value_at(solution, "Food", foods, h),
            value_at(solution, "Car", cars, h),
            value_at(solution, "Phone", phones, h),
            value_at(solution, "Occupation", occupations, h),
            value_at(solution, "Drink", drinks, h),
        ])

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()