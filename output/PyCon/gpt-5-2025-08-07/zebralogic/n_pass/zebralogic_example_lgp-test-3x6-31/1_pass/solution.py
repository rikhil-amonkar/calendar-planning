import json
from constraint import Problem, AllDifferentConstraint

def var(category, value):
    return f"{category}_{value}"

def main():
    houses = [1, 2, 3]

    categories = {
        "Name": ["Eric", "Peter", "Arnold"],
        "Drink": ["milk", "water", "tea"],
        "Vacation": ["mountain", "city", "beach"],
        "HouseStyle": ["colonial", "victorian", "ranch"],
        "Animal": ["cat", "bird", "horse"],
        "Birthday": ["jan", "sept", "april"],
    }

    problem = Problem()

    # Add variables
    for category, values in categories.items():
        for v in values:
            problem.addVariable(var(category, v), houses)

    # Uniqueness within each category
    for category, values in categories.items():
        problem.addConstraint(
            AllDifferentConstraint(),
            [var(category, v) for v in values]
        )

    # Clues:
    # 1. Colonial is somewhere to the left of milk.
    problem.addConstraint(
        lambda col, milk: col < milk,
        (var("HouseStyle", "colonial"), var("Drink", "milk"))
    )

    # 2. City is directly left of Victorian.
    problem.addConstraint(
        lambda city, victorian: city + 1 == victorian,
        (var("Vacation", "city"), var("HouseStyle", "victorian"))
    )

    # 3. January is directly left of the cat lover.
    problem.addConstraint(
        lambda jan, cat: jan + 1 == cat,
        (var("Birthday", "jan"), var("Animal", "cat"))
    )

    # 4. Water drinker is the person who enjoys mountain retreats.
    problem.addConstraint(
        lambda water, mountain: water == mountain,
        (var("Drink", "water"), var("Vacation", "mountain"))
    )

    # 5. The person who keeps horses is Peter.
    problem.addConstraint(
        lambda horse, peter: horse == peter,
        (var("Animal", "horse"), var("Name", "Peter"))
    )

    # 6. Victorian is somewhere to the right of beach vacations.
    problem.addConstraint(
        lambda victorian, beach: victorian > beach,
        (var("HouseStyle", "victorian"), var("Vacation", "beach"))
    )

    # 7. Peter prefers city breaks.
    problem.addConstraint(
        lambda peter, city: peter == city,
        (var("Name", "Peter"), var("Vacation", "city"))
    )

    # 8. Mountain retreats corresponds to April birthday.
    problem.addConstraint(
        lambda mountain, april: mountain == april,
        (var("Vacation", "mountain"), var("Birthday", "april"))
    )

    # 9. Eric drinks water.
    problem.addConstraint(
        lambda eric, water: eric == water,
        (var("Name", "Eric"), var("Drink", "water"))
    )

    solutions = problem.getSolutions()
    if not solutions:
        raise ValueError("No solution found for the given puzzle.")

    sol = solutions[0]

    header = ["House", "Name", "Drink", "Vacation", "HouseStyle", "Animal", "Birthday"]
    rows = []
    for h in houses:
        name = next(v for v in categories["Name"] if sol[var("Name", v)] == h)
        drink = next(v for v in categories["Drink"] if sol[var("Drink", v)] == h)
        vacation = next(v for v in categories["Vacation"] if sol[var("Vacation", v)] == h)
        house_style = next(v for v in categories["HouseStyle"] if sol[var("HouseStyle", v)] == h)
        animal = next(v for v in categories["Animal"] if sol[var("Animal", v)] == h)
        birthday = next(v for v in categories["Birthday"] if sol[var("Birthday", v)] == h)

        rows.append([str(h), name, drink, vacation, house_style, animal, birthday])

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()