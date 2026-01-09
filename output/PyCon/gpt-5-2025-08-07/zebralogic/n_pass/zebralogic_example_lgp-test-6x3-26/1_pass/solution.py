import json
import sys
import subprocess

# Ensure python-constraint is available
try:
    from constraint import Problem, AllDifferentConstraint
except ImportError:
    subprocess.check_call([sys.executable, "-m", "pip", "install", "python-constraint"])
    from constraint import Problem, AllDifferentConstraint


def solve_puzzle():
    problem = Problem()

    houses = range(1, 7)

    names = ["Alice", "Eric", "Bob", "Peter", "Arnold", "Carol"]
    heights = ["very tall", "tall", "super tall", "average", "very short", "short"]
    phones = ["oneplus 9", "google pixel 6", "samsung galaxy s21", "iphone 13", "huawei p50", "xiaomi mi 11"]

    # Add variables for each attribute value with domain 1..6 (house positions)
    for n in names:
        problem.addVariable(n, houses)
    for h in heights:
        problem.addVariable(h, houses)
    for p in phones:
        problem.addVariable(p, houses)

    # AllDifferent constraints within each category
    problem.addConstraint(AllDifferentConstraint(), names)
    problem.addConstraint(AllDifferentConstraint(), heights)
    problem.addConstraint(AllDifferentConstraint(), phones)

    # Clues:
    # 1. Bob is directly left of the person who is tall.
    problem.addConstraint(lambda bob, tall: bob == tall - 1, ("Bob", "tall"))

    # 2. Peter is somewhere to the left of the person who uses an iPhone 13.
    problem.addConstraint(lambda peter, iphone: peter < iphone, ("Peter", "iphone 13"))

    # 3. The person who is very short is somewhere to the right of the person who uses a Google Pixel 6.
    problem.addConstraint(lambda vshort, pixel: vshort > pixel, ("very short", "google pixel 6"))

    # 4. Carol is the person who is very tall.
    problem.addConstraint(lambda carol, vt: carol == vt, ("Carol", "very tall"))

    # 5. There is one house between the person who uses a Google Pixel 6 and the person who is short.
    problem.addConstraint(lambda pixel, short: abs(pixel - short) == 2, ("google pixel 6", "short"))

    # 6. The person who uses a Samsung Galaxy S21 is not in the first house.
    problem.addConstraint(lambda s21: s21 != 1, ("samsung galaxy s21",))

    # 7. The person who uses a OnePlus 9 is directly left of the person who is short.
    problem.addConstraint(lambda op9, short: op9 == short - 1, ("oneplus 9", "short"))

    # 8. The person who is tall is Arnold.
    problem.addConstraint(lambda tall, arnold: tall == arnold, ("tall", "Arnold"))

    # 9. The person who is super tall is in the first house.
    problem.addConstraint(lambda st: st == 1, ("super tall",))

    # 10. The person who uses a Xiaomi Mi 11 is Carol.
    problem.addConstraint(lambda mi11, carol: mi11 == carol, ("xiaomi mi 11", "Carol"))

    # 11. The person who uses a Google Pixel 6 is somewhere to the right of Eric.
    problem.addConstraint(lambda pixel, eric: pixel > eric, ("google pixel 6", "Eric"))

    # 12. The person who is short is in the sixth house.
    problem.addConstraint(lambda short: short == 6, ("short",))

    solutions = problem.getSolutions()
    if not solutions:
        raise ValueError("No solution found for the given puzzle constraints.")

    # Assuming a unique solution; take the first
    sol = solutions[0]

    # Build inverse mappings from house to attributes
    name_by_house = {}
    for n in names:
        name_by_house[sol[n]] = n

    height_by_house = {}
    for h in heights:
        height_by_house[sol[h]] = h

    phone_by_house = {}
    for p in phones:
        phone_by_house[sol[p]] = p

    rows = []
    for house in range(1, 7):
        rows.append([
            str(house),
            name_by_house[house],
            height_by_house[house],
            phone_by_house[house]
        ])

    output = {
        "solution": {
            "header": ["House", "Name", "Height", "PhoneModel"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    solve_puzzle()