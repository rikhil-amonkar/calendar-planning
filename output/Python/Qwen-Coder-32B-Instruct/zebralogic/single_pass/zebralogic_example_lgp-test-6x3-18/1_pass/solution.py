import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Arnold", "Eric", "Bob", "Alice", "Carol", "Peter"]
    mothers_names = ["Sarah", "Holly", "Janelle", "Aniya", "Penny", "Kailyn"]
    pets = ["hamster", "dog", "bird", "cat", "fish", "rabbit"]

    for name_permutation in itertools.permutations(names):
        for mother_permutation in itertools.permutations(mothers_names):
            for pet_permutation in itertools.permutations(pets):
                # Assign permutations to variables for easier reference
                name_map = dict(zip(houses, name_permutation))
                mother_map = dict(zip(houses, mother_permutation))
                pet_map = dict(zip(houses, pet_permutation))

                # Check all constraints
                if (name_map[2] != "Bob" and
                    abs(pet_map.index("cat") - pet_map.index("rabbit")) == 2 and
                    pet_map.index("cat") + 1 == mother_map.index("Holly") and
                    pet_map.index("hamster") + 1 == pet_map.index("rabbit") and
                    name_map[pet_map.index("rabbit")] == "Eric" and
                    abs(pet_map.index("dog") - pet_map.index("cat")) == 1 and
                    mother_map[pet_map.index("cat")] == "Janelle" and
                    name_map.index("Alice") + 1 == name_map.index("Carol") and
                    mother_map[name_map.index("Carol")] == "Aniya" and
                    name_map[pet_map.index("cat")] == "Arnold" and
                    mother_map[pet_map.index("rabbit")] == "Kailyn" and
                    mother_map[pet_map.index("fish")] == "Sarah"):
                    
                    # If all constraints are satisfied, construct the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Mother's Name", "Pet"],
                            "rows": []
                        }
                    }
                    for house in houses:
                        solution["solution"]["rows"].append([
                            str(house),
                            name_map[house],
                            mother_map[house],
                            pet_map[house]
                        ])
                    
                    return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())