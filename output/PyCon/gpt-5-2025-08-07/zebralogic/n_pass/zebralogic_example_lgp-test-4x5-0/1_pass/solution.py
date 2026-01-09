import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    houses = [1, 2, 3, 4]

    names = ["Eric", "Peter", "Arnold", "Alice"]
    smoothies = ["dragonfruit", "cherry", "desert", "watermelon"]
    cigars = ["blue master", "pall mall", "dunhill", "prince"]
    heights = ["tall", "average", "short", "very short"]
    phones = ["google pixel 6", "samsung galaxy s21", "iphone 13", "oneplus 9"]

    problem = Problem()

    # Add variables for each attribute mapping to house positions
    for attr in names + smoothies + cigars + heights + phones:
        problem.addVariable(attr, houses)

    # AllDifferent constraints for each category
    problem.addConstraint(AllDifferentConstraint(), names)
    problem.addConstraint(AllDifferentConstraint(), smoothies)
    problem.addConstraint(AllDifferentConstraint(), cigars)
    problem.addConstraint(AllDifferentConstraint(), heights)
    problem.addConstraint(AllDifferentConstraint(), phones)

    # Clues as constraints
    # 1. The Dragonfruit smoothie lover is Eric.
    problem.addConstraint(lambda dragonfruit, Eric: dragonfruit == Eric, ("dragonfruit", "Eric"))

    # 2. The Dunhill smoker is the person who likes Cherry smoothies.
    problem.addConstraint(lambda dunhill, cherry: dunhill == cherry, ("dunhill", "cherry"))

    # 3. The Samsung Galaxy S21 user is directly left of the iPhone 13 user.
    problem.addConstraint(lambda s, i: s == i - 1, ("samsung galaxy s21", "iphone 13"))

    # 4. The Dunhill smoker is somewhere to the right of the very short person.
    problem.addConstraint(lambda dunhill, very_short: dunhill > very_short, ("dunhill", "very short"))

    # 5. The Watermelon smoothie lover is somewhere to the right of the Desert smoothie lover.
    problem.addConstraint(lambda watermelon, desert: watermelon > desert, ("watermelon", "desert"))

    # 6. The Prince smoker is the person who uses a OnePlus 9.
    problem.addConstraint(lambda prince, oneplus: prince == oneplus, ("prince", "oneplus 9"))

    # 7. The person who is tall is in the third house.
    problem.addConstraint(lambda tall: tall == 3, ("tall",))

    # 8. The very short person is the iPhone 13 user.
    problem.addConstraint(lambda very_short, iphone: very_short == iphone, ("very short", "iphone 13"))

    # 9. The Blue Master smoker is not in the first house.
    problem.addConstraint(lambda blue_master: blue_master != 1, ("blue master",))

    # 10. The Dunhill smoker is the person who is short.
    problem.addConstraint(lambda dunhill, short: dunhill == short, ("dunhill", "short"))

    # 11. Peter is not in the third house.
    problem.addConstraint(lambda Peter: Peter != 3, ("Peter",))

    # 12. Arnold is the person who uses a Google Pixel 6.
    problem.addConstraint(lambda Arnold, pixel6: Arnold == pixel6, ("Arnold", "google pixel 6"))

    # 13. The Dragonfruit smoothie lover is the Pall Mall smoker.
    problem.addConstraint(lambda dragonfruit, pall_mall: dragonfruit == pall_mall, ("dragonfruit", "pall mall"))

    solutions = problem.getSolutions()

    if not solutions:
        raise ValueError("No solution found for the given puzzle.")
    # Choose the first solution (should be unique)
    sol = solutions[0]

    # Invert mappings to get attributes by house
    def by_house(category):
        return {sol[item]: item for item in category}

    names_by_house = by_house(names)
    smoothies_by_house = by_house(smoothies)
    cigars_by_house = by_house(cigars)
    heights_by_house = by_house(heights)
    phones_by_house = by_house(phones)

    rows = []
    for h in houses:
        rows.append([
            str(h),
            names_by_house[h],
            smoothies_by_house[h],
            cigars_by_house[h],
            heights_by_house[h],
            phones_by_house[h],
        ])

    output = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Cigar", "Height", "PhoneModel"],
            "rows": rows
        }
    }
    return output

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, ensure_ascii=False, indent=2))