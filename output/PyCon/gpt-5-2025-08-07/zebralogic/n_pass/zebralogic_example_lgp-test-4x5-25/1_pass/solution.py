import json
import sys

# Ensure python-constraint is available
try:
    from constraint import Problem, AllDifferentConstraint
except ImportError:
    import subprocess
    subprocess.check_call([sys.executable, "-m", "pip", "install", "python-constraint"])
    from constraint import Problem, AllDifferentConstraint

def main():
    houses = [1, 2, 3, 4]

    # Define categories and their labels
    categories = {
        "Name": ["Arnold", "Peter", "Eric", "Alice"],
        "Style": ["craftsman", "colonial", "victorian", "ranch"],
        "Hair": ["red", "blonde", "black", "brown"],
        "Child": ["Bella", "Fred", "Meredith", "Samantha"],
        "Genre": ["mystery", "fantasy", "romance", "science fiction"],
    }

    problem = Problem()

    # Add variables for each label with domain as house numbers
    for cat, labels in categories.items():
        for label in labels:
            problem.addVariable((cat, label), houses)

    # All-different constraints within each category
    for cat, labels in categories.items():
        problem.addConstraint(AllDifferentConstraint(), [(cat, label) for label in labels])

    # Clues as constraints:

    # 1. The person in a Craftsman-style house is in the third house.
    problem.addConstraint(lambda x: x == 3, [("Style", "craftsman")])

    # 2. Alice is the person who loves romance books.
    problem.addConstraint(lambda a, b: a == b, [("Name", "Alice"), ("Genre", "romance")])

    # 3. The person who has brown hair is in the fourth house.
    problem.addConstraint(lambda x: x == 4, [("Hair", "brown")])

    # 4. The person's child is named Samantha is in the fourth house.
    problem.addConstraint(lambda x: x == 4, [("Child", "Samantha")])

    # 5. The person in a ranch-style home is somewhere to the right of the person who has red hair.
    problem.addConstraint(lambda ranch, red: ranch > red, [("Style", "ranch"), ("Hair", "red")])

    # 6. Peter is the person's child is named Bella. => Peter's child is Bella => same house
    problem.addConstraint(lambda p, c: p == c, [("Name", "Peter"), ("Child", "Bella")])

    # 7. Arnold is the person who has red hair.
    problem.addConstraint(lambda a, r: a == r, [("Name", "Arnold"), ("Hair", "red")])

    # 8. Alice is the person living in a colonial-style house.
    problem.addConstraint(lambda a, c: a == c, [("Name", "Alice"), ("Style", "colonial")])

    # 9. The person who has black hair is in the second house.
    problem.addConstraint(lambda x: x == 2, [("Hair", "black")])

    # 10. The person who loves fantasy books is Peter.
    problem.addConstraint(lambda g, p: g == p, [("Genre", "fantasy"), ("Name", "Peter")])

    # 11. Arnold is the person's child is named Meredith. => Arnold's child is Meredith
    problem.addConstraint(lambda a, m: a == m, [("Name", "Arnold"), ("Child", "Meredith")])

    # 12. The person who has black hair is Eric.
    problem.addConstraint(lambda b, e: b == e, [("Hair", "black"), ("Name", "Eric")])

    # 13. The person who loves science fiction books is Arnold.
    problem.addConstraint(lambda s, a: s == a, [("Genre", "science fiction"), ("Name", "Arnold")])

    solutions = problem.getSolutions()
    if not solutions:
        # If no solution, still output valid JSON structure with empty rows
        output = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "HairColor", "Children", "BookGenre"],
                "rows": []
            }
        }
        print(json.dumps(output, ensure_ascii=False))
        return

    # Assuming unique solution; choose the first
    sol = solutions[0]

    def value_at_house(category, house_no):
        for label in categories[category]:
            if sol[(category, label)] == house_no:
                return label
        return None

    rows = []
    for h in houses:
        name = value_at_house("Name", h)
        style = value_at_house("Style", h)
        hair = value_at_house("Hair", h)
        child = value_at_house("Child", h)
        genre = value_at_house("Genre", h)
        rows.append([str(h), name, style, hair, child, genre])

    output = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "HairColor", "Children", "BookGenre"],
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False))

if __name__ == "__main__":
    main()