import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    houses = range(1, 7)

    names = ["Alice", "Arnold", "Carol", "Peter", "Bob", "Eric"]
    phones = ["huawei p50", "iphone 13", "xiaomi mi 11", "oneplus 9", "samsung galaxy s21", "google pixel 6"]

    problem = Problem()

    # Variables: positions (1..6) for each name and each phone
    for n in names:
        problem.addVariable(("Name", n), houses)
    for p in phones:
        problem.addVariable(("Phone", p), houses)

    # All different constraints
    problem.addConstraint(AllDifferentConstraint(), [("Name", n) for n in names])
    problem.addConstraint(AllDifferentConstraint(), [("Phone", p) for p in phones])

    # Clues:
    # 1. The person who uses an iPhone 13 is Alice.
    problem.addConstraint(lambda a, p: a == p, (("Name", "Alice"), ("Phone", "iphone 13")))
    # 2. The person who uses a Huawei P50 is in the first house.
    problem.addConstraint(lambda x: x == 1, (("Phone", "huawei p50"),))
    # 3. The person who uses a OnePlus 9 is in the sixth house.
    problem.addConstraint(lambda x: x == 6, (("Phone", "oneplus 9"),))
    # 4. The person who uses a Google Pixel 6 is not in the second house.
    problem.addConstraint(lambda x: x != 2, (("Phone", "google pixel 6"),))
    # 5. The person who uses an iPhone 13 is not in the second house.
    problem.addConstraint(lambda x: x != 2, (("Phone", "iphone 13"),))
    # 6. There is one house between Bob and Carol.
    problem.addConstraint(lambda b, c: abs(b - c) == 2, (("Name", "Bob"), ("Name", "Carol")))
    # 7. The person who uses a Huawei P50 is Eric.
    problem.addConstraint(lambda e, h: e == h, (("Name", "Eric"), ("Phone", "huawei p50")))
    # 8. The person who uses a Xiaomi Mi 11 is in the third house.
    problem.addConstraint(lambda x: x == 3, (("Phone", "xiaomi mi 11"),))
    # 9. Alice is somewhere to the left of Carol.
    problem.addConstraint(lambda a, c: a < c, (("Name", "Alice"), ("Name", "Carol")))
    # 10. Arnold is the person who uses a OnePlus 9.
    problem.addConstraint(lambda ar, op: ar == op, (("Name", "Arnold"), ("Phone", "oneplus 9")))

    solution = problem.getSolution()
    if not solution:
        raise ValueError("No solution found for the given puzzle.")

    # Build rows by house number
    rows = []
    for h in range(1, 7):
        # Find the name at house h
        name_at_h = next(n for n in names if solution[("Name", n)] == h)
        phone_at_h = next(p for p in phones if solution[("Phone", p)] == h)
        rows.append([str(h), name_at_h, phone_at_h])

    output = {
        "solution": {
            "header": ["House", "Name", "PhoneModel"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    solve_puzzle()