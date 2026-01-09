import json
from constraint import Problem, AllDifferentConstraint

def main():
    houses = range(1, 6)

    names = ["Bob", "Eric", "Arnold", "Alice", "Peter"]
    colors = ["blue", "green", "white", "yellow", "red"]
    phones = ["huawei p50", "samsung galaxy s21", "oneplus 9", "iphone 13", "google pixel 6"]
    occupations = ["artist", "teacher", "doctor", "engineer", "lawyer"]

    problem = Problem()

    # Add variables for each attribute value with domain 1..5
    for n in names:
        problem.addVariable(n, houses)
    for c in colors:
        problem.addVariable(c, houses)
    for p in phones:
        problem.addVariable(p, houses)
    for o in occupations:
        problem.addVariable(o, houses)

    # All-different constraints within each category
    problem.addConstraint(AllDifferentConstraint(), names)
    problem.addConstraint(AllDifferentConstraint(), colors)
    problem.addConstraint(AllDifferentConstraint(), phones)
    problem.addConstraint(AllDifferentConstraint(), occupations)

    # Clues constraints

    # 1. Engineer is somewhere to the right of the lawyer.
    problem.addConstraint(lambda eng, law: eng > law, ("engineer", "lawyer"))

    # 2. Bob is in the second house.
    problem.addConstraint(lambda b: b == 2, ("Bob",))

    # 3. Samsung Galaxy S21 user is the doctor.
    problem.addConstraint(lambda s21, doc: s21 == doc, ("samsung galaxy s21", "doctor"))

    # 4. The doctor loves blue.
    problem.addConstraint(lambda doc, blue: doc == blue, ("doctor", "blue"))

    # 5. Green is not in the fifth house.
    problem.addConstraint(lambda g: g != 5, ("green",))

    # 6. The lawyer uses a OnePlus 9.
    problem.addConstraint(lambda law, op9: law == op9, ("lawyer", "oneplus 9"))

    # 7. Blue is directly left of red.
    problem.addConstraint(lambda b, r: r - b == 1, ("blue", "red"))

    # 8. The lawyer is somewhere to the right of the Samsung Galaxy S21 user.
    problem.addConstraint(lambda law, s21: law > s21, ("lawyer", "samsung galaxy s21"))

    # 9. One house between Google Pixel 6 and Huawei P50.
    problem.addConstraint(lambda pix, hua: abs(pix - hua) == 2, ("google pixel 6", "huawei p50"))

    # 10. Arnold is the engineer.
    problem.addConstraint(lambda arn, eng: arn == eng, ("Arnold", "engineer"))

    # 11. Alice loves yellow.
    problem.addConstraint(lambda alice, yellow: alice == yellow, ("Alice", "yellow"))

    # 12. Google Pixel 6 user is Eric.
    problem.addConstraint(lambda pix, eric: pix == eric, ("google pixel 6", "Eric"))

    # 13. Google Pixel 6 user is the teacher.
    problem.addConstraint(lambda pix, teacher: pix == teacher, ("google pixel 6", "teacher"))

    # 14. Red is somewhere to the right of the teacher.
    problem.addConstraint(lambda red, teacher: red > teacher, ("red", "teacher"))

    solutions = problem.getSolutions()

    if not solutions:
        raise RuntimeError("No solution found for the puzzle.")

    # Take the first (should be unique)
    sol = solutions[0]

    # Build rows by house
    rows = []
    for h in range(1, 6):
        # Find the name at house h
        name_at_h = next(n for n in names if sol[n] == h)
        color_at_h = next(c for c in colors if sol[c] == h)
        phone_at_h = next(p for p in phones if sol[p] == h)
        occupation_at_h = next(o for o in occupations if sol[o] == h)

        rows.append([str(h), name_at_h, color_at_h, phone_at_h, occupation_at_h])

    output = {
        "solution": {
            "header": ["House", "Name", "Color", "PhoneModel", "Occupation"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()