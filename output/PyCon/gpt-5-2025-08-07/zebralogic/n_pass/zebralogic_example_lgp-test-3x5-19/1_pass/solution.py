import json
from constraint import Problem, AllDifferentConstraint

def main():
    houses = [1, 2, 3]

    categories = {
        "Name": ["Arnold", "Peter", "Eric"],
        "Occupation": ["doctor", "teacher", "engineer"],
        "Education": ["associate", "high school", "bachelor"],
        "Smoothie": ["desert", "cherry", "watermelon"],
        "Hobby": ["gardening", "cooking", "photography"],
    }

    problem = Problem()

    # Add variables for each attribute item with domain as houses
    for category, items in categories.items():
        for item in items:
            problem.addVariable(f"{category}_{item}", houses)

    # AllDifferent constraints within each category
    for category, items in categories.items():
        problem.addConstraint(
            AllDifferentConstraint(), [f"{category}_{item}" for item in items]
        )

    # Clues as constraints:

    # 1. The Desert smoothie lover is the person who is a doctor.
    problem.addConstraint(
        lambda s_desert, o_doctor: s_desert == o_doctor,
        ["Smoothie_desert", "Occupation_doctor"],
    )

    # 2. Arnold is not in the third house.
    problem.addConstraint(lambda n_arnold: n_arnold != 3, ["Name_Arnold"])

    # 3. The person who likes Cherry smoothies is somewhere to the right of Peter.
    problem.addConstraint(
        lambda s_cherry, n_peter: s_cherry > n_peter,
        ["Smoothie_cherry", "Name_Peter"],
    )

    # 4. The person who loves cooking is in the second house.
    problem.addConstraint(lambda h_cooking: h_cooking == 2, ["Hobby_cooking"])

    # 5. The person who loves cooking is Peter.
    problem.addConstraint(
        lambda h_cooking, n_peter: h_cooking == n_peter,
        ["Hobby_cooking", "Name_Peter"],
    )

    # 6. The person with an associate's degree is somewhere to the right of the person who enjoys gardening.
    problem.addConstraint(
        lambda e_associate, h_gardening: e_associate > h_gardening,
        ["Education_associate", "Hobby_gardening"],
    )

    # 7. The person with a bachelor's degree is somewhere to the right of the Desert smoothie lover.
    problem.addConstraint(
        lambda e_bachelor, s_desert: e_bachelor > s_desert,
        ["Education_bachelor", "Smoothie_desert"],
    )

    # 8. The person who loves cooking is the person who is a doctor.
    problem.addConstraint(
        lambda h_cooking, o_doctor: h_cooking == o_doctor,
        ["Hobby_cooking", "Occupation_doctor"],
    )

    # 9. The photography enthusiast is the person who is a teacher.
    problem.addConstraint(
        lambda h_photo, o_teacher: h_photo == o_teacher,
        ["Hobby_photography", "Occupation_teacher"],
    )

    solutions = problem.getSolutions()
    if not solutions:
        # In the unlikely event no solution, output empty structure
        output = {
            "solution": {
                "header": ["House", "Name", "Occupation", "Education", "Smoothie", "Hobby"],
                "rows": []
            }
        }
        print(json.dumps(output, indent=2))
        return

    # Choose the first solution (should be unique for this puzzle)
    sol = solutions[0]

    def value_at_house(category, house):
        for item in categories[category]:
            if sol[f"{category}_{item}"] == house:
                return item
        return None

    rows = []
    for house in houses:
        rows.append([
            str(house),
            value_at_house("Name", house),
            value_at_house("Occupation", house),
            value_at_house("Education", house),
            value_at_house("Smoothie", house),
            value_at_house("Hobby", house),
        ])

    output = {
        "solution": {
            "header": ["House", "Name", "Occupation", "Education", "Smoothie", "Hobby"],
            "rows": rows
        }
    }

    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()