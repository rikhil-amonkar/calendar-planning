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
    # Define categories and values
    categories = {
        "Name": ["Peter", "Alice", "Eric", "Arnold"],
        "Mother": ["Janelle", "Holly", "Aniya", "Kailyn"],
        "Smoothie": ["watermelon", "dragonfruit", "desert", "cherry"],
        "Height": ["tall", "average", "short", "very short"],
        "Education": ["high school", "associate", "master", "bachelor"],
    }

    # Create variable names mapping (sanitized)
    def sanitize(val):
        return val.replace(" ", "_")

    varnames = {
        cat: {val: f"{cat}_{sanitize(val)}" for val in vals}
        for cat, vals in categories.items()
    }

    problem = Problem()

    # Add variables with domain 1..4 (house positions)
    houses = [1, 2, 3, 4]
    for cat in categories:
        for val in categories[cat]:
            problem.addVariable(varnames[cat][val], houses)

    # All-different within each category
    for cat in categories:
        problem.addConstraint(AllDifferentConstraint(), [varnames[cat][val] for val in categories[cat]])

    # Helper to get var id
    def V(cat, val):
        return varnames[cat][val]

    # Constraints from clues:

    # 1. The person whose mother's name is Janelle is in the third house.
    problem.addConstraint(lambda x: x == 3, [V("Mother", "Janelle")])

    # 2. The Desert smoothie lover is the person with a master's degree.
    problem.addConstraint(lambda d, m: d == m, [V("Smoothie", "desert"), V("Education", "master")])

    # 3. The Desert smoothie lover is not in the first house.
    problem.addConstraint(lambda x: x != 1, [V("Smoothie", "desert")])

    # 4. The person who is very short is somewhere to the left of the person with a high school diploma.
    problem.addConstraint(lambda vs, hs: vs < hs, [V("Height", "very short"), V("Education", "high school")])

    # 5. Eric and the person who likes Cherry smoothies are next to each other.
    problem.addConstraint(lambda e, c: abs(e - c) == 1, [V("Name", "Eric"), V("Smoothie", "cherry")])

    # 6. The person with a high school diploma is not in the third house.
    problem.addConstraint(lambda x: x != 3, [V("Education", "high school")])

    # 7. The person whose mother's name is Kailyn is the person with an associate's degree.
    problem.addConstraint(lambda k, a: k == a, [V("Mother", "Kailyn"), V("Education", "associate")])

    # 8. The person who likes Cherry smoothies is The person whose mother's name is Aniya.
    problem.addConstraint(lambda c, a: c == a, [V("Smoothie", "cherry"), V("Mother", "Aniya")])

    # 9. The person who is tall is The person whose mother's name is Janelle.
    problem.addConstraint(lambda t, j: t == j, [V("Height", "tall"), V("Mother", "Janelle")])

    # 10. Arnold is somewhere to the right of the person who has an average height.
    problem.addConstraint(lambda arn, avg: arn > avg, [V("Name", "Arnold"), V("Height", "average")])

    # 11. The Dragonfruit smoothie lover is directly left of the person who is short.
    problem.addConstraint(lambda d, s: d + 1 == s, [V("Smoothie", "dragonfruit"), V("Height", "short")])

    # 12. The person who is tall is Alice.
    problem.addConstraint(lambda t, a: t == a, [V("Height", "tall"), V("Name", "Alice")])

    # Solve
    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No solution found for the given puzzle.")

    sol = solutions[0]

    # Build per-house mapping for each category
    def invert_category(cat):
        inv = {}
        for val in categories[cat]:
            pos = sol[V(cat, val)]
            inv[pos] = val
        return inv

    name_by_house = invert_category("Name")
    mother_by_house = invert_category("Mother")
    smoothie_by_house = invert_category("Smoothie")
    height_by_house = invert_category("Height")
    education_by_house = invert_category("Education")

    rows = []
    for h in sorted(houses):
        row = [
            str(h),
            name_by_house[h],
            mother_by_house[h],
            smoothie_by_house[h],
            height_by_house[h],
            education_by_house[h],
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": ["House", "Name", "Mother", "Smoothie", "Height", "Education"],
            "rows": rows,
        }
    }

    print(json.dumps(output, ensure_ascii=False))


if __name__ == "__main__":
    main()