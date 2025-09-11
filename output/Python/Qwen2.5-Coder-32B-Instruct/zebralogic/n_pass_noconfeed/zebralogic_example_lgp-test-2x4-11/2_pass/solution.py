import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Eric", "Arnold"]
    hobbies = ["gardening", "photography"]
    pets = ["cat", "dog"]
    heights = ["short", "very short"]

    # Generate all possible combinations of permutations for the two houses
    all_combinations = list(itertools.product(
        itertools.permutations(names),
        itertools.permutations(hobbies),
        itertools.permutations(pets),
        itertools.permutations(heights)
    ))

    # Filter combinations based on the given clues
    for comb in all_combinations:
        name_perm, hobby_perm, pet_perm, height_perm = comb
        name1, name2 = name_perm
        hobby1, hobby2 = hobby_perm
        pet1, pet2 = pet_perm
        height1, height2 = height_perm

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