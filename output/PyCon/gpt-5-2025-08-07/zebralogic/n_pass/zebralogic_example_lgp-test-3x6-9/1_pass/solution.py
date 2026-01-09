import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define categories and their items
    houses = [1, 2, 3]
    categories = {
        "Name": ["Peter", "Arnold", "Eric"],
        "CarModel": ["toyota camry", "ford f150", "tesla model 3"],
        "HouseStyle": ["ranch", "colonial", "victorian"],
        "Pet": ["cat", "dog", "fish"],
        "Occupation": ["engineer", "doctor", "teacher"],
        "Vacation": ["city", "mountain", "beach"],
    }

    def V(cat, item):
        return f"{cat}:{item}"

    problem = Problem()

    # Add variables: each item maps to a house number
    for cat, items in categories.items():
        for item in items:
            problem.addVariable(V(cat, item), houses)

    # Each category must be a permutation of houses
    for cat, items in categories.items():
        problem.addConstraint(AllDifferentConstraint(), [V(cat, item) for item in items])

    # Apply clues as constraints

    # 1. The person with an aquarium of fish is in the first house.
    problem.addConstraint(lambda h: h == 1, [V("Pet", "fish")])

    # 2. The person who owns a Toyota Camry is in the second house.
    problem.addConstraint(lambda h: h == 2, [V("CarModel", "toyota camry")])

    # 3. The person who enjoys mountain retreats is not in the second house.
    problem.addConstraint(lambda h: h != 2, [V("Vacation", "mountain")])

    # 4. The person who prefers city breaks is not in the second house.
    problem.addConstraint(lambda h: h != 2, [V("Vacation", "city")])

    # 5. The person in a ranch-style home is somewhere to the left of Peter.
    problem.addConstraint(
        lambda ranch, peter: ranch < peter,
        [V("HouseStyle", "ranch"), V("Name", "Peter")]
    )

    # 6. The person who owns a Toyota Camry is directly left of the person living in a colonial-style house.
    problem.addConstraint(
        lambda camry, colonial: camry + 1 == colonial,
        [V("CarModel", "toyota camry"), V("HouseStyle", "colonial")]
    )

    # 7. Arnold is the person who has a cat.
    problem.addConstraint(
        lambda arnold, cat: arnold == cat,
        [V("Name", "Arnold"), V("Pet", "cat")]
    )

    # 8. Eric is somewhere to the left of the person who enjoys mountain retreats.
    problem.addConstraint(
        lambda eric, mountain: eric < mountain,
        [V("Name", "Eric"), V("Vacation", "mountain")]
    )

    # 9. The person who is an engineer is not in the third house.
    problem.addConstraint(lambda eng: eng != 3, [V("Occupation", "engineer")])

    # 10. The person who owns a Tesla Model 3 is somewhere to the left of the person who is a teacher.
    problem.addConstraint(
        lambda tesla, teacher: tesla < teacher,
        [V("CarModel", "tesla model 3"), V("Occupation", "teacher")]
    )

    # 11. The person who owns a dog is the person who is an engineer.
    problem.addConstraint(
        lambda dog, engineer: dog == engineer,
        [V("Pet", "dog"), V("Occupation", "engineer")]
    )

    solutions = problem.getSolutions()
    if not solutions:
        raise RuntimeError("No solution found for the given puzzle.")

    sol = solutions[0]

    def find_item(category, house_num):
        for item in categories[category]:
            if sol[V(category, item)] == house_num:
                return item
        raise RuntimeError(f"No item found in category {category} for house {house_num}")

    header = ["House", "Name", "CarModel", "HouseStyle", "Pet", "Occupation", "Vacation"]
    rows = []
    for h in houses:
        row = [
            str(h),
            find_item("Name", h),
            find_item("CarModel", h),
            find_item("HouseStyle", h),
            find_item("Pet", h),
            find_item("Occupation", h),
            find_item("Vacation", h),
        ]
        rows.append(row)

    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

    print(json.dumps(output, ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()