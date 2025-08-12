import itertools
import json

def solve_puzzle():
    # Define the possible values for each attribute
    names = ["Eric", "Arnold", "Peter"]
    smoothies = ["desert", "watermelon", "cherry"]
    books = ["science fiction", "romance", "mystery"]

    # Generate all possible permutations for each attribute
    permutations = list(itertools.permutations(names)) * \
                   list(itertools.permutations(smoothies)) * \
                   list(itertools.permutations(books))

    # Define the clues as functions
    def clue1(houses):
        cherry_index = houses[1].index("cherry")
        mystery_index = houses[2].index("mystery")
        return cherry_index < mystery_index

    def clue2(houses):
        return houses[2][1] == "Arnold"

    def clue3(houses):
        return houses[2][0] != "science fiction"

    def clue4(houses):
        desert_index = houses[1].index("desert")
        mystery_index = houses[2].index("mystery")
        return desert_index == mystery_index - 1

    def clue5(houses):
        return houses[0][0] == "Peter"

    # Check each permutation to see if it satisfies all clues
    for perm in permutations:
        houses = [list(t) for t in zip(*[iter(perm)]*3)]
        if clue1(houses) and clue2(houses) and clue3(houses) and clue4(houses) and clue5(houses):
            solution = {
                "solution": {
                    "header": ["House", "Name", "Favorite Smoothie", "Favorite Book Genre"],
                    "rows": [
                        ["1", houses[0][0], houses[1][0], houses[2][0]],
                        ["2", houses[0][1], houses[1][1], houses[2][1]],
                        ["3", houses[0][2], houses[1][2], houses[2][2]]
                    ]
                }
            }
            return json.dumps(solution, indent=2)

# Run the solver and print the result
print(solve_puzzle())