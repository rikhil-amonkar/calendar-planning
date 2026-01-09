import json
from constraint import Problem, AllDifferentConstraint

def main():
    houses = [1, 2, 3]

    categories = {
        "Name": ["Arnold", "Peter", "Eric"],
        "Animal": ["bird", "horse", "cat"],
        "Birthday": ["jan", "sept", "april"],
        "Hobby": ["photography", "cooking", "gardening"],
        "Drink": ["milk", "water", "tea"],
        "HairColor": ["black", "brown", "blonde"],
    }

    problem = Problem()

    # Add variables for each value with domain as house numbers
    for category, values in categories.items():
        for v in values:
            problem.addVariable(f"{category}_{v}", houses)

    # Each category values must be in different houses
    for category, values in categories.items():
        problem.addConstraint(AllDifferentConstraint(), [f"{category}_{v}" for v in values])

    # Clues:
    # 1. The person who has brown hair is the person who loves cooking.
    problem.addConstraint(lambda hb, hc: hb == hc, ("HairColor_brown", "Hobby_cooking"))

    # 2. The person whose birthday is in April is in the third house.
    problem.addConstraint(lambda x: x == 3, ("Birthday_april",))

    # 3. Eric is not in the first house.
    problem.addConstraint(lambda x: x != 1, ("Name_Eric",))

    # 4. The cat lover is in the second house.
    problem.addConstraint(lambda x: x == 2, ("Animal_cat",))

    # 5. The person who has blonde hair is somewhere to the left of the person who likes milk.
    problem.addConstraint(lambda blonde, milk: blonde < milk, ("HairColor_blonde", "Drink_milk"))

    # 6. The person who enjoys gardening is the person who likes milk.
    problem.addConstraint(lambda g, m: g == m, ("Hobby_gardening", "Drink_milk"))

    # 7. The cat lover is the person who has brown hair.
    problem.addConstraint(lambda cat, brown: cat == brown, ("Animal_cat", "HairColor_brown"))

    # 8. Arnold is the bird keeper.
    problem.addConstraint(lambda arnold, bird: arnold == bird, ("Name_Arnold", "Animal_bird"))

    # 9. The one who only drinks water is the photography enthusiast.
    problem.addConstraint(lambda water, photo: water == photo, ("Drink_water", "Hobby_photography"))

    # 10. The person whose birthday is in September is directly left of Arnold.
    problem.addConstraint(lambda sept, arnold: sept + 1 == arnold, ("Birthday_sept", "Name_Arnold"))

    solutions = problem.getSolutions()

    if not solutions:
        raise RuntimeError("No solution found")

    # Assuming unique solution; take the first
    sol = solutions[0]

    def value_for_house(category, house):
        for v in categories[category]:
            if sol[f"{category}_{v}"] == house:
                return v
        return None

    header = ["House", "Name", "Animal", "Birthday", "Hobby", "Drink", "HairColor"]
    rows = []
    for h in houses:
        rows.append([
            str(h),
            value_for_house("Name", h),
            value_for_house("Animal", h),
            value_for_house("Birthday", h),
            value_for_house("Hobby", h),
            value_for_house("Drink", h),
            value_for_house("HairColor", h),
        ])

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()