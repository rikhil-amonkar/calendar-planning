import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Eric", "Arnold"]
    hobbies = ["gardening", "photography"]
    pets = ["cat", "dog"]
    heights = ["short", "very short"]

    # Generate all possible permutations for the two houses
    all_permutations = list(itertools.permutations(names)) * \
                       list(itertools.permutations(hobbies)) * \
                       list(itertools.permutations(pets)) * \
                       list(itertools.permutations(heights))

    # Function to check if a permutation satisfies all the clues
    def is_valid_solution(permutation):
        name1, name2 = permutation[0]
        hobby1, hobby2 = permutation[1]
        pet1, pet2 = permutation[2]
        height1, height2 = permutation[3]

        # Clue 1: The person who is very short is the photography enthusiast.
        if height1 == "very short" and hobby1 != "photography":
            return False
        if height2 == "very short" and hobby2 != "photography":
            return False

        # Clue 2: Eric is the person who is very short.
        if name1 == "Eric" and height1 != "very short":
            return False
        if name2 == "Eric" and height2 != "very short":
            return False

        # Clue 3: The person who has a cat is somewhere to the right of the person who is very short.
        if height1 == "very short" and pet1 == "cat":
            return False
        if height2 == "very short" and pet2 == "cat":
            return False

        return True

    # Find the valid solution
    for permutation in all_permutations:
        if is_valid_solution(permutation):
            name1, name2 = permutation[0]
            hobby1, hobby2 = permutation[1]
            pet1, pet2 = permutation[2]
            height1, height2 = permutation[3]

            solution = {
                "solution": {
                    "header": ["House", "Name", "Hobby", "Pet", "Height"],
                    "rows": [
                        ["1", name1, hobby1, pet1, height1],
                        ["2", name2, hobby2, pet2, height2]
                    ]
                }
            }

            print(json.dumps(solution))
            return

# Run the solver
solve_puzzle()