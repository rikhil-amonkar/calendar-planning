import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5]
    names = ["Alice", "Eric", "Arnold", "Bob", "Peter"]
    flowers = ["tulips", "roses", "lilies", "daffodils", "carnations"]
    animals = ["dog", "horse", "cat", "bird", "fish"]

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for flower_perm in itertools.permutations(flowers):
            for animal_perm in itertools.permutations(animals):
                # Unpack permutations for easier access
                house_name = dict(zip(houses, name_perm))
                house_flower = dict(zip(houses, flower_perm))
                house_animal = dict(zip(houses, animal_perm))

                # Check all clues
                if (house_name[2] == "Alice" and
                    house_flower[house_animal["bird"]] == "lilies" and
                    name_perm.index("Peter") > name_perm.index(house_flower["tulips"]) and
                    house_animal[house_flower["daffodils"]] == "fish" and
                    house_animal["horse"] == "Eric" and
                    abs(name_perm.index("Bob") - name_perm.index(house_animal["dog"])) == 3 and
                    house_animal["fish"] + 1 == name_perm.index("Bob") and
                    house_name[house_animal["horse"] - 1] == "Alice" and
                    name_perm.index(house_flower["carnations"]) + 1 == name_perm.index(house_flower["tulips"]) and
                    house_animal["cat"] != 1):
                    
                    # Construct the solution in the required format
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Flower", "Animal"],
                            "rows": [
                                [str(house), house_name[house], house_flower[house], house_animal[house]]
                                for house in houses
                            ]
                        }
                    }
                    return json.dumps(solution, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())