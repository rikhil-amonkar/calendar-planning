import itertools
import json

def solve_puzzle():
    # Define the possible values for each characteristic
    names = ['Eric', 'Arnold', 'Peter']
    heights = ['short', 'very short', 'average']
    houses = [1, 2, 3]

    # Filter permutations based on the given clues
    for name_permutation in itertools.permutations(names):
        for height_permutation in itertools.permutations(heights):
            # Unpack the permutations for easier access
            name1, name2, name3 = name_permutation
            height1, height2, height3 = height_permutation

            # Apply the clues
            if (name1 != 'Eric' and  # Clue 1
                height1 == 'very short' and  # Clue 3
                (height1 == 'very short' and (height2 == 'short' or height3 == 'short')) and  # Clue 2
                name1 != 'Arnold'):  # Clue 4

                # If all clues are satisfied, construct the solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Height"],
                        "rows": [
                            ["1", name1, height1],
                            ["2", name2, height2],
                            ["3", name3, height3]
                        ]
                    }
                }

                # Output the solution as JSON
                print(json.dumps(solution, indent=2))
                return

# Run the function to solve the puzzle
solve_puzzle()