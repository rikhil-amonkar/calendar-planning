import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Peter", "Alice", "Eric", "Arnold"]
    mothers = ["Janelle", "Holly", "Aniya", "Kailyn"]
    smoothies = ["watermelon", "dragonfruit", "desert", "cherry"]
    heights = ["tall", "average", "short", "very short"]
    educations = ["high school", "associate", "master", "bachelor"]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(mothers)) * \
                       list(itertools.permutations(smoothies)) * \
                       list(itertools.permutations(heights)) * \
                       list(itertools.permutations(educations))

    # Define the clues as functions
    def clue1(houses):
        return houses[2][1] == "Janelle"

    def clue2(houses):
        for house in houses:
            if house[2] == "desert" and house[4] == "master":
                return True
        return False

    def clue3(houses):
        return houses[0][2] != "desert"

    def clue4(houses):
        for i in range(len(houses) - 1):
            if houses[i][3] == "very short" and houses[i + 1][4] == "high school":
                return True
        return False

    def clue5(houses):
        for i in range(len(houses) - 1):
            if houses[i][0] == "Eric" and houses[i + 1][2] == "cherry":
                return True
            if houses[i + 1][0] == "Eric" and houses[i][2] == "cherry":
                return True
        return False

    def clue6(houses):
        return houses[2][4] != "high school"

    def clue7(houses):
        for house in houses:
            if house[1] == "Kailyn" and house[4] == "associate":
                return True
        return False

    def clue8(houses):
        for house in houses:
            if house[2] == "cherry" and house[1] == "Aniya":
                return True
        return False

    def clue9(houses):
        return houses[2][3] == "tall"

    def clue10(houses):
        for i in range(len(houses) - 1):
            if houses[i][3] == "average" and houses[i + 1][0] == "Arnold":
                return True
        return False

    def clue11(houses):
        for i in range(len(houses) - 1):
            if houses[i][2] == "dragonfruit" and houses[i + 1][3] == "short":
                return True
        return False

    def clue12(houses):
        for house in houses:
            if house[0] == "Alice" and house[3] == "tall":
                return True
        return False

    # Check all permutations against the clues
    for permutation in itertools.product(all_permutations, repeat=1):
        names_perm, mothers_perm, smoothies_perm, heights_perm, educations_perm = permutation[0][:5]
        houses = list(zip(range(1, 5), names_perm, mothers_perm, smoothies_perm, heights_perm, educations_perm))
        if all([clue1(houses), clue2(houses), clue3(houses), clue4(houses),
                clue5(houses), clue6(houses), clue7(houses), clue8(houses),
                clue9(houses), clue10(houses), clue11(houses), clue12(houses)]):
            # Format the solution as JSON
            solution = {
                "solution": {
                    "header": ["House", "Name", "Mother", "Smoothie", "Height", "Education"],
                    "rows": [[str(house[0]), house[1], house[2], house[3], house[4], house[5]] for house in houses]
                }
            }
            print(json.dumps(solution, indent=2))
            return

# Run the solver
solve_puzzle()