import json
from z3 import Solver, Int, Distinct, And, Implies

def solve_puzzle():
    # Domains
    names = ["Arnold", "Eric"]
    educations = ["associate", "high school"]
    heights = ["short", "very short"]
    foods = ["grilled cheese", "pizza"]
    drinks = ["tea", "water"]

    idx_name = {v: i for i, v in enumerate(names)}
    idx_edu = {v: i for i, v in enumerate(educations)}
    idx_height = {v: i for i, v in enumerate(heights)}
    idx_food = {v: i for i, v in enumerate(foods)}
    idx_drink = {v: i for i, v in enumerate(drinks)}

    num_houses = 2
    s = Solver()

    # Variables per house (0-based indexing for houses)
    Name = [Int(f"Name_{i}") for i in range(num_houses)]
    Edu = [Int(f"Edu_{i}") for i in range(num_houses)]
    Height = [Int(f"Height_{i}") for i in range(num_houses)]
    Food = [Int(f"Food_{i}") for i in range(num_houses)]
    Drink = [Int(f"Drink_{i}") for i in range(num_houses)]

    # Domain constraints
    for i in range(num_houses):
        s.add(Name[i] >= 0, Name[i] < len(names))
        s.add(Edu[i] >= 0, Edu[i] < len(educations))
        s.add(Height[i] >= 0, Height[i] < len(heights))
        s.add(Food[i] >= 0, Food[i] < len(foods))
        s.add(Drink[i] >= 0, Drink[i] < len(drinks))

    # Uniqueness across houses
    s.add(Distinct(Name))
    s.add(Distinct(Edu))
    s.add(Distinct(Height))
    s.add(Distinct(Food))
    s.add(Distinct(Drink))

    # Clues:
    # 1. The person who is very short is the person who is a pizza lover.
    for i in range(num_houses):
        s.add(Implies(Height[i] == idx_height["very short"], Food[i] == idx_food["pizza"]))
        s.add(Implies(Food[i] == idx_food["pizza"], Height[i] == idx_height["very short"]))

    # 2. The person who loves eating grilled cheese is in the second house.
    s.add(Food[1] == idx_food["grilled cheese"])

    # 3. The person with a high school diploma is the person who is a pizza lover.
    for i in range(num_houses):
        s.add(Implies(Edu[i] == idx_edu["high school"], Food[i] == idx_food["pizza"]))
        s.add(Implies(Food[i] == idx_food["pizza"], Edu[i] == idx_edu["high school"]))

    # 4. The tea drinker is the person who loves eating grilled cheese.
    for i in range(num_houses):
        s.add(Implies(Drink[i] == idx_drink["tea"], Food[i] == idx_food["grilled cheese"]))
        s.add(Implies(Food[i] == idx_food["grilled cheese"], Drink[i] == idx_drink["tea"]))

    # 5. Arnold is the person who is a pizza lover.
    for i in range(num_houses):
        s.add(Implies(Name[i] == idx_name["Arnold"], Food[i] == idx_food["pizza"]))
        s.add(Implies(Food[i] == idx_food["pizza"], Name[i] == idx_name["Arnold"]))

    if s.check() != 1:  # 1 == sat
        raise RuntimeError("No solution found")

    m = s.model()

    rows = []
    for house in range(num_houses):
        row = [
            str(house + 1),
            names[m.evaluate(Name[house]).as_long()],
            educations[m.evaluate(Edu[house]).as_long()],
            heights[m.evaluate(Height[house]).as_long()],
            foods[m.evaluate(Food[house]).as_long()],
            drinks[m.evaluate(Drink[house]).as_long()],
        ]
        rows.append(row)

    result = {
        "solution": {
            "header": ["House", "Name", "Education", "Height", "Food", "Drink"],
            "rows": rows
        }
    }
    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()