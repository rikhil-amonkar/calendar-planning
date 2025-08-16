import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4]
    names = ['Peter', 'Arnold', 'Eric', 'Alice']
    pets = ['bird', 'fish', 'dog', 'cat']

    # Generate all possible permutations for names and pets
    for name_permutation in itertools.permutations(names):
        for pet_permutation in itertools.permutations(pets):
            # Unpack permutations for easier access
            name_to_house = {name: house for house, name in zip(houses, name_permutation)}
            pet_to_house = {pet: house for house, pet in zip(houses, pet_permutation)}

            # Check constraints
            if (name_to_house['Alice'] < pet_to_house['dog'] and
                name_to_house['Eric'] != 1 and
                pet_to_house['bird'] == name_to_house['Eric'] and
                abs(name_to_house['Peter'] - pet_to_house['fish']) == 2 and
                name_to_house['Alice'] != 1 and
                pet_to_house['fish'] == name_to_house['Arnold']):
                
                # If all constraints are satisfied, prepare the solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Pet"],
                        "rows": []
                    }
                }
                for house in houses:
                    name = name_permutation[house - 1]
                    pet = pet_permutation[house - 1]
                    solution["solution"]["rows"].append([str(house), name, pet])
                
                return json.dumps(solution, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())