import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Eric", "Peter", "Arnold"]
    smoothies = ["cherry", "watermelon", "desert"]
    flowers = ["carnations", "lilies", "daffodils"]
    animals = ["cat", "horse", "bird"]
    hobbies = ["photography", "cooking", "gardening"]

    # Generate all possible permutations for each category
    permutations = list(itertools.permutations(names)) + \
                   list(itertools.permutations(smoothies)) + \
                   list(itertools.permutations(flowers)) + \
                   list(itertools.permutations(animals)) + \
                   list(itertools.permutations(hobbies))

    # Iterate over all possible combinations of permutations
    for names_perm in permutations[:6]:
        for smoothies_perm in permutations[6:12]:
            for flowers_perm in permutations[12:18]:
                for animals_perm in permutations[18:24]:
                    for hobbies_perm in permutations[24:]:
                        # Unpack the permutations into variables for easier access
                        name1, name2, name3 = names_perm
                        smoothie1, smoothie2, smoothie3 = smoothies_perm
                        flower1, flower2, flower3 = flowers_perm
                        animal1, animal2, animal3 = animals_perm
                        hobby1, hobby2, hobby3 = hobbies_perm

                        # Apply the clues to check if the current combination is valid
                        if (animal2 == "horse" and hobby1 == "photography") or \
                           (animal1 == "horse" and hobby2 == "photography") and \
                           animal3 == "bird" and smoothie3 == "cherry" and \
                           hobby2 == "cooking" and smoothie2 == "desert" and \
                           hobby3 == "gardening" and flower3 == "carnations" and \
                           name2 == "Peter" and smoothie2 == "desert" and \
                           flower2 == "daffodils" and animal2 == "horse" and \
                           smoothie2 == "watermelon" and hobby1 == "photography":

                            # Construct the solution in the required format
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Smoothie", "Flower", "Animal", "Hobby"],
                                    "rows": [
                                        ["1", name1, smoothie1, flower1, animal1, hobby1],
                                        ["2", name2, smoothie2, flower2, animal2, hobby2],
                                        ["3", name3, smoothie3, flower3, animal3, hobby3]
                                    ]
                                }
                            }

                            # Output the solution as a JSON-formatted string
                            print(json.dumps(solution, indent=2))
                            return

# Call the function to solve the puzzle
solve_puzzle()