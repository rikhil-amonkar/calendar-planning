import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Arnold", "Eric"]
    educations = ["associate", "high school"]
    heights = ["short", "very short"]
    foods = ["grilled cheese", "pizza"]
    drinks = ["tea", "water"]

    # Generate all possible permutations for the two houses
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(educations)) * \
                       list(itertools.permutations(heights)) * \
                       list(itertools.permutations(foods)) * \
                       list(itertools.permutations(drinks))

    # Define the constraints
    def is_valid_solution(permutation):
        # Unpack the permutation into separate lists for each category
        name1, name2 = permutation[0]
        edu1, edu2 = permutation[1]
        height1, height2 = permutation[2]
        food1, food2 = permutation[3]
        drink1, drink2 = permutation[4]

        # Apply the clues
        if height1 == "very short" and food1 != "pizza":
            return False
        if height2 == "very short" and food2 != "pizza":
            return False
        if food1 == "grilled cheese" and name1 != "Eric":
            return False
        if food2 == "grilled cheese" and name2 != "Arnold":
            return False
        if edu1 == "high school" and food1 != "pizza":
            return False
        if edu2 == "high school" and food2 != "pizza":
            return False
        if drink1 == "tea" and food1 != "grilled cheese":
            return False
        if drink2 == "tea" and food2 != "grilled cheese":
            return False
        if food1 == "pizza" and name1 != "Arnold":
            return False
        if food2 == "pizza" and name2 != "Arnold":
            return False

        return True

    # Find the valid solution
    for permutation in itertools.product(*[list(itertools.permutations(category)) for category in [names, educations, heights, foods, drinks]]):
        if is_valid_solution(permutation):
            name1, name2 = permutation[0]
            edu1, edu2 = permutation[1]
            height1, height2 = permutation[2]
            food1, food2 = permutation[3]
            drink1, drink2 = permutation[4]

            solution = {
                "solution": {
                    "header": ["House", "Name", "Education", "Height", "Food", "Drink"],
                    "rows": [
                        ["1", name1, edu1, height1, food1, drink1],
                        ["2", name2, edu2, height2, food2, drink2]
                    ]
                }
            }

            print(json.dumps(solution, indent=2))
            return

solve_puzzle()