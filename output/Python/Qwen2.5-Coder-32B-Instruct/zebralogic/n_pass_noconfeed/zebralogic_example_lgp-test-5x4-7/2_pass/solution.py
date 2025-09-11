import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]
    names = ['Alice', 'Peter', 'Bob', 'Eric', 'Arnold']
    smoothies = ['lime', 'dragonfruit', 'desert', 'watermelon', 'cherry']
    animals = ['horse', 'dog', 'bird', 'fish', 'cat']
    nationalities = ['german', 'swede', 'norwegian', 'brit', 'dane']

    for name_perm in itertools.permutations(names):
        for smoothie_perm in itertools.permutations(smoothies):
            for animal_perm in itertools.permutations(animals):
                for nationality_perm in itertools.permutations(nationalities):
                    # Assign permutations to variables for readability
                    name_map = dict(zip(houses, name_perm))
                    smoothie_map = dict(zip(houses, smoothie_perm))
                    animal_map = dict(zip(houses, animal_perm))
                    nationality_map = dict(zip(houses, nationality_perm))

                    # Apply constraints
                    if (any(nationality_map[house] == 'swede' and animal_map[house + 1] == 'dog' for house in houses if house < 5) and
                        any(animal_map[i] == 'dog' and nationality_map[i + 2] == 'brit' for i in range(len(houses) - 2)) and
                        nationality_map[3] == 'dane' and animal_map[3] == 'horse' and
                        any(animal_map[i] == 'cat' and animal_map[j] == 'bird' and i < j for i in range(len(houses)) for j in range(len(houses))) and
                        any(animal_map[i] == 'dog' and smoothie_map[i + 1] == 'lime' for i in range(len(houses) - 1)) and
                        any(name_map[house] == 'Eric' and animal_map[house] == 'cat' for house in houses) and
                        any(name_map[house] == 'Bob' and animal_map[house] == 'bird' for house in houses) and
                        any(name_map[i] == 'Peter' and smoothie_map[i - 1] == 'cherry' for i in range(1, len(houses))) and
                        any(animal_map[house] == 'bird' and smoothie_map[house] == 'watermelon' for house in houses) and
                        any(animal_map[house] == 'dog' and smoothie_map[house] == 'desert' for house in houses) and
                        any(nationality_map[house] == 'norwegian' and name_map[house] == 'Alice' for house in houses)):

                        # If all constraints are satisfied, construct the solution
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Smoothie", "Animal", "Nationality"],
                                "rows": [
                                    [str(house), name_map[house], smoothie_map[house], animal_map[house], nationality_map[house]]
                                    for house in houses
                                ]
                            }
                        }

                        return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())