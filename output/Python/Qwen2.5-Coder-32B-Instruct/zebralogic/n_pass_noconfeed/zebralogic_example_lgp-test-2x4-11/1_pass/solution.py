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

    # Filter permutations based on the given clues
    for perm in all_permutations:
        name1, name2 = perm[0:2]
        hobby1, hobby2 = perm[2:4]
        pet1, pet2 = perm[4:6]
        height1, height2 = perm[6:8]

        # Clue 1: The person who is very short is the photography enthusiast.
        if height1 == "very short" and hobby1 != "photography":
            continue
        if height2 == "very short" and hobby2 != "photography":
            continue

        # Clue 2: Eric is the person who is very short.
        if height1 == "very short" and name1 != "Eric":
            continue
        if height2 == "very short" and name2 != "Eric":
            continue

        # Clue 3: The person who has a cat is somewhere to the right of the person who is very short.
        if height1 == "very short" and pet1 == "cat":
            continue
        if height2 == "very short" and pet2 == "cat":
            continue
        if height1 == "very short" and pet2 != "cat":
            continue

        # If all clues are satisfied, construct the solution
        solution = {
            "solution": {
                "header": ["House", "Name", "Hobby", "Pet", "Height"],
                "rows": [
                    ["1", name1, hobby1, pet1, height1],
                    ["2", name2, hobby2, pet2, height2]
                ]
            }
        }

        # Output the solution as JSON
        print(json.dumps(solution, indent=2))
        return

# Run the function to solve the puzzle
solve_puzzle()