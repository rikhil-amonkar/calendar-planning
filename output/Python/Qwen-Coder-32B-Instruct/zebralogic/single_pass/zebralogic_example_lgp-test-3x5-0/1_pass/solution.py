import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Peter", "Arnold", "Eric"]
    books = ["science fiction", "mystery", "romance"]
    smoothies = ["watermelon", "desert", "cherry"]
    birthdays = ["april", "jan", "sept"]
    heights = ["average", "very short", "short"]

    # Generate all possible permutations for each category
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(books)) * \
                       list(itertools.permutations(smoothies)) * \
                       list(itertools.permutations(birthdays)) * \
                       list(itertools.permutations(heights))

    # Define the clues as functions
    def clue1(houses):
        return houses[1][2] != "cherry"

    def clue2(houses):
        return houses[[i for i, h in enumerate(houses) if h[1] == "Arnold"][0]][1] == "mystery"

    def clue3(houses):
        return houses[0][3] != "jan"

    def clue4(houses):
        return houses[[i for i, h in enumerate(houses) if h[4] == "very short"][0]][1] == "romance"

    def clue5(houses):
        return houses[[i for i, h in enumerate(houses) if h[1] == "mystery"][0]][3] == "sept"

    def clue6(houses):
        return houses[[i for i, h in enumerate(houses) if h[4] == "average"][0]][2] == "desert"

    def clue7(houses):
        return houses[0][0] == "Eric"

    def clue8(houses):
        return houses[[i for i, h in enumerate(houses) if h[2] == "watermelon"][0]][4] == "short"

    def clue9(houses):
        return houses[[i for i, h in enumerate(houses) if h[2] == "watermelon"][0]][0] == "Eric"

    # Check each permutation against all clues
    for perm in all_permutations:
        houses = [
            [perm[0][0], perm[1][0], perm[2][0], perm[3][0], perm[4][0]],
            [perm[0][1], perm[1][1], perm[2][1], perm[3][1], perm[4][1]],
            [perm[0][2], perm[1][2], perm[2][2], perm[3][2], perm[4][2]]
        ]
        if (clue1(houses) and clue2(houses) and clue3(houses) and
            clue4(houses) and clue5(houses) and clue6(houses) and
            clue7(houses) and clue8(houses) and clue9(houses)):
            # Format the solution as required
            solution = {
                "solution": {
                    "header": ["House", "Name", "Favorite Book Genre", "Favorite Smoothie", "Birthday Month", "Height"],
                    "rows": [
                        ["1", houses[0][0], houses[0][1], houses[0][2], houses[0][3], houses[0][4]],
                        ["2", houses[1][0], houses[1][1], houses[1][2], houses[1][3], houses[1][4]],
                        ["3", houses[2][0], houses[2][1], houses[2][2], houses[2][3], houses[2][4]]
                    ]
                }
            }
            print(json.dumps(solution, indent=2))
            return

solve_puzzle()