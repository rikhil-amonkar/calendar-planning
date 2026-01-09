import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    houses = [1, 2, 3]

    # Categories
    names = ["Eric", "Arnold", "Peter"]
    phones = ["iphone 13", "samsung galaxy s21", "google pixel 6"]
    heights = ["very short", "average", "short"]
    styles = ["colonial", "ranch", "victorian"]
    cars = ["tesla model 3", "toyota camry", "ford f150"]

    problem = Problem()

    # Add variables for each attribute value with domain of houses
    for val in names + phones + heights + styles + cars:
        problem.addVariable(val, houses)

    # All different within each category
    problem.addConstraint(AllDifferentConstraint(), names)
    problem.addConstraint(AllDifferentConstraint(), phones)
    problem.addConstraint(AllDifferentConstraint(), heights)
    problem.addConstraint(AllDifferentConstraint(), styles)
    problem.addConstraint(AllDifferentConstraint(), cars)

    # Clues:
    # 1. Peter is somewhere to the right of Eric.
    problem.addConstraint(lambda p, e: p > e, ("Peter", "Eric"))

    # 2. The person living in a colonial-style house is in the second house.
    problem.addConstraint(lambda c: c == 2, ("colonial",))

    # 3. The person who owns a Tesla Model 3 is the person who is very short.
    problem.addConstraint(lambda t, v: t == v, ("tesla model 3", "very short"))

    # 4. The person who is short is directly left of the person who uses a Samsung Galaxy S21.
    problem.addConstraint(lambda sh, sg: sh == sg - 1, ("short", "samsung galaxy s21"))

    # 5. The person who uses an iPhone 13 is directly left of the person who uses a Google Pixel 6.
    problem.addConstraint(lambda ip, gp: ip == gp - 1, ("iphone 13", "google pixel 6"))

    # 6. The person living in a colonial-style house is somewhere to the right of the person in a ranch-style home.
    problem.addConstraint(lambda col, ra: col > ra, ("colonial", "ranch"))

    # 7. Arnold is in the second house.
    problem.addConstraint(lambda a: a == 2, ("Arnold",))

    # 8. The person who owns a Ford F-150 is somewhere to the right of the person who owns a Toyota Camry.
    problem.addConstraint(lambda f, c: f > c, ("ford f150", "toyota camry"))

    # 9. The person who has an average height is in the first house.
    problem.addConstraint(lambda avg: avg == 1, ("average",))

    solutions = problem.getSolutions()
    if not solutions:
        raise ValueError("No solution found for the given puzzle constraints.")

    # Assume unique solution; take the first
    sol = solutions[0]

    # Build reverse lookups for each category: house -> value
    def invert(category):
        return {sol[item]: item for item in category}

    name_by_house = invert(names)
    phone_by_house = invert(phones)
    height_by_house = invert(heights)
    style_by_house = invert(styles)
    car_by_house = invert(cars)

    header = ["House", "Name", "PhoneModel", "Height", "HouseStyle", "CarModel"]
    rows = []
    for h in sorted(houses):
        rows.append([
            str(h),
            name_by_house[h],
            phone_by_house[h],
            height_by_house[h],
            style_by_house[h],
            car_by_house[h],
        ])

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    solve_puzzle()