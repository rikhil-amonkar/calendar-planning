import json
from constraint import Problem, AllDifferentConstraint

def main():
    houses = [1, 2, 3]

    # Attributes
    Names = ["Eric", "Peter", "Arnold"]
    Drinks = ["tea", "water", "milk"]
    Nationalities = ["dane", "brit", "swede"]
    Educations = ["high school", "associate", "bachelor"]
    HouseStyles = ["victorian", "colonial", "ranch"]
    Smoothies = ["cherry", "watermelon", "desert"]

    # Set up problem
    problem = Problem()

    # Add variables: each attribute value maps to a house number
    for val in Names + Drinks + Nationalities + Educations + HouseStyles + Smoothies:
        problem.addVariable(val, houses)

    # All-different constraints within each category
    problem.addConstraint(AllDifferentConstraint(), Names)
    problem.addConstraint(AllDifferentConstraint(), Drinks)
    problem.addConstraint(AllDifferentConstraint(), Nationalities)
    problem.addConstraint(AllDifferentConstraint(), Educations)
    problem.addConstraint(AllDifferentConstraint(), HouseStyles)
    problem.addConstraint(AllDifferentConstraint(), Smoothies)

    # Clues as constraints

    # 1. There is one house between Eric and the tea drinker.
    problem.addConstraint(lambda eric, tea: abs(eric - tea) == 2, ("Eric", "tea"))

    # 2. The person who likes milk is the person in a ranch-style home.
    problem.addConstraint(lambda milk, ranch: milk == ranch, ("milk", "ranch"))

    # 3. The person with a bachelor's degree is in the second house.
    problem.addConstraint(lambda bachelor: bachelor == 2, ("bachelor",))

    # 4. The person with a high school diploma is the Dane.
    problem.addConstraint(lambda hs, dane: hs == dane, ("high school", "dane"))

    # 5. The Desert smoothie lover is the Swedish person.
    problem.addConstraint(lambda desert, swede: desert == swede, ("desert", "swede"))

    # 6. The person residing in a Victorian house is not in the first house.
    problem.addConstraint(lambda victorian: victorian != 1, ("victorian",))

    # 7. The person who likes Cherry smoothies is the person living in a colonial-style house.
    problem.addConstraint(lambda cherry, colonial: cherry == colonial, ("cherry", "colonial"))

    # 8. Arnold is somewhere to the right of the person residing in a Victorian house.
    problem.addConstraint(lambda arnold, victorian: arnold > victorian, ("Arnold", "victorian"))

    # 9. The person in a ranch-style home is the person with a high school diploma.
    problem.addConstraint(lambda ranch, hs: ranch == hs, ("ranch", "high school"))

    solutions = problem.getSolutions()

    if not solutions:
        raise RuntimeError("No solution found for the given puzzle.")

    # Select the first solution (should be unique)
    sol = solutions[0]

    def value_for_house(category_values, house_num):
        for v in category_values:
            if sol[v] == house_num:
                return v
        raise ValueError(f"No value found for house {house_num} in {category_values}")

    header = ["House", "Name", "Drink", "Nationality", "Education", "HouseStyle", "Smoothie"]
    rows = []
    for h in sorted(houses):
        row = [
            str(h),
            value_for_house(Names, h),
            value_for_house(Drinks, h),
            value_for_house(Nationalities, h),
            value_for_house(Educations, h),
            value_for_house(HouseStyles, h),
            value_for_house(Smoothies, h),
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