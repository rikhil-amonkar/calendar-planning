import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Arnold", "Eric", "Peter", "Alice"]
    occupations = ["doctor", "engineer", "artist", "teacher"]

    # Generate all possible permutations for names and occupations
    permutations = list(itertools.permutations(names))
    occupation_permutations = list(itertools.permutations(occupations))

    # Function to check if a given permutation satisfies all the clues
    def is_valid_solution(name_order, occupation_order):
        # Unpack the permutations for easier access
        house1, house2, house3, house4 = name_order
        occ1, occ2, occ3, occ4 = occupation_order

        # Apply the clues
        # Clue 1: There are two houses between Eric and Peter.
        eric_index = name_order.index("Eric")
        peter_index = name_order.index("Peter")
        if abs(eric_index - peter_index) != 2:
            return False

        # Clue 2: The person who is a teacher is Peter.
        if occupation_order[peter_index] != "teacher":
            return False

        # Clue 3: Peter is not in the first house.
        if peter_index == 0:
            return False

        # Clue 4: There is one house between the person who is a doctor and Alice.
        alice_index = name_order.index("Alice")
        doctor_index = occupation_order.index("doctor")
        if abs(alice_index - doctor_index) != 1:
            return False

        # Clue 5: The person who is an artist is Alice.
        if occupation_order[alice_index] != "artist":
            return False

        return True

    # Iterate over all possible permutations to find the valid solution
    for name_order in permutations:
        for occupation_order in occupation_permutations:
            if is_valid_solution(name_order, occupation_order):
                # Prepare the solution in the required format
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Occupation"],
                        "rows": [
                            ["1", name_order[0], occupation_order[0]],
                            ["2", name_order[1], occupation_order[1]],
                            ["3", name_order[2], occupation_order[2]],
                            ["4", name_order[3], occupation_order[3]]
                        ]
                    }
                }
                return json.dumps(solution, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())