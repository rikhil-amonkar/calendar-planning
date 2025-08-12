import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4]
    names = ["Peter", "Arnold", "Eric", "Alice"]
    pets = ["bird", "fish", "dog", "cat"]

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for pet_perm in itertools.permutations(pets):
            # Unpack permutations for easier access
            name_house = dict(zip(houses, name_perm))
            pet_house = dict(zip(houses, pet_perm))

            # Check constraints
            if (name_house[pet_house.index("dog")] > name_house[name_perm.index("Alice")] and
                name_house["Eric"] != 1 and
                pet_house[name_house.index("Eric")] == "bird" and
                abs(name_house[name_perm.index("Peter")] - name_house[pet_house.index("fish")]) == 2 and
                name_house["Alice"] != 1 and
                pet_house[name_house.index("Arnold")] == "fish"):
                
                # Prepare the solution in the required format
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Pet"],
                        "rows": []
                    }
                }
                
                for house in houses:
                    solution["solution"]["rows"].append([
                        str(house),
                        name_house[house],
                        pet_house[house]
                    ])
                
                return json.dumps(solution, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())