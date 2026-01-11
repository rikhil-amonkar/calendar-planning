import itertools
import json

def solve_puzzle():
    # Define the possible values for each attribute
    names = ["Peter", "Arnold", "Eric", "Alice"]
    pets = ["bird", "fish", "dog", "cat"]

    # Generate all possible permutations of names and pets
    all_permutations = list(itertools.permutations(names))
    pet_permutations = list(itertools.permutations(pets))

    # Function to check if a configuration satisfies all constraints
    def is_valid(config):
        name_to_house = {config[i][0]: i + 1 for i in range(4)}
        pet_to_house = {config[i][1]: i + 1 for i in range(4)}

        # Constraint 1: Dog owner is to the right of Alice
        if name_to_house["Alice"] >= name_to_house.get("Peter", 0) or name_to_house["Alice"] >= pet_to_house.get("dog", 0):
            return False

        # Constraint 2: Eric is not in the first house
        if name_to_house.get("Eric", 0) == 1:
            return False

        # Constraint 3: Eric keeps a bird
        if name_to_house.get("Eric", 0) != pet_to_house.get("bird", 0):
            return False

        # Constraint 4: One house between fish owner and Peter
        if abs(name_to_house.get("Peter", 0) - pet_to_house.get("fish", 0)) != 2:
            return False

        # Constraint 5: Alice is not in the first house
        if name_to_house.get("Alice", 0) == 1:
            return False

        # Constraint 6: Arnold keeps fish
        if name_to_house.get("Arnold", 0) != pet_to_house.get("fish", 0):
            return False

        return True

    # Iterate through all permutations to find a valid solution
    for name_perm in all_permutations:
        for pet_perm in pet_permutations:
            config = list(zip(name_perm, pet_perm))
            if is_valid(config):
                # Format the solution as required
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Pet"],
                        "rows": [["1", config[0][0], config[0][1]],
                                 ["2", config[1][0], config[1][1]],
                                 ["3", config[2][0], config[2][1]],
                                 ["4", config[3][0], config[3][1]]]
                    }
                }
                return json.dumps(solution, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())