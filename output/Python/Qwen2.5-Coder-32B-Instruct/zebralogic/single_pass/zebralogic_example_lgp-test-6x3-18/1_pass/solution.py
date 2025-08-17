import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ["Arnold", "Eric", "Bob", "Alice", "Carol", "Peter"]
    mothers = ["Sarah", "Holly", "Janelle", "Aniya", "Penny", "Kailyn"]
    pets = ["hamster", "dog", "bird", "cat", "fish", "rabbit"]

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for mother_perm in itertools.permutations(mothers):
            for pet_perm in itertools.permutations(pets):
                # Create a dictionary for easy access
                house_dict = {house: {"name": name, "mother": mother, "pet": pet}
                              for house, name, mother, pet in zip(houses, name_perm, mother_perm, pet_perm)}

                # Check all constraints
                if (house_dict[2]["name"] != "Bob" and
                    abs(house_dict.index(next(house for house, info in house_dict.items() if info["pet"] == "cat")) -
                        house_dict.index(next(house for house, info in house_dict.items() if info["pet"] == "rabbit"))) == 3 and
                    house_dict.index(next(house for house, info in house_dict.items() if info["pet"] == "cat")) + 1 ==
                    house_dict.index(next(house for house, info in house_dict.items() if info["mother"] == "Holly")) and
                    house_dict.index(next(house for house, info in house_dict.items() if info["pet"] == "hamster")) + 1 ==
                    house_dict.index(next(house for house, info in house_dict.items() if info["pet"] == "rabbit")) and
                    house_dict[next(house for house, info in house_dict.items() if info["pet"] == "rabbit")]["name"] == "Eric" and
                    abs(house_dict.index(next(house for house, info in house_dict.items() if info["pet"] == "dog")) -
                        house_dict.index(next(house for house, info in house_dict.items() if info["pet"] == "cat"))) == 2 and
                    house_dict[next(house for house, info in house_dict.items() if info["pet"] == "cat")]["mother"] == "Janelle" and
                    house_dict.index(next(house for house, info in house_dict.items() if info["name"] == "Alice")) + 1 ==
                    house_dict.index(next(house for house, info in house_dict.items() if info["name"] == "Carol")) and
                    house_dict[next(house for house, info in house_dict.items() if info["name"] == "Carol")]["mother"] == "Aniya" and
                    house_dict[next(house for house, info in house_dict.items() if info["pet"] == "cat")]["name"] == "Arnold" and
                    house_dict[next(house for house, info in house_dict.items() if info["mother"] == "Kailyn")]["pet"] == "rabbit" and
                    house_dict[next(house for house, info in house_dict.items() if info["mother"] == "Sarah")]["pet"] == "fish"):
                    
                    # Format the solution as required
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Mother", "Pet"],
                            "rows": [[str(house), info["name"], info["mother"], info["pet"]] for house, info in house_dict.items()]
                        }
                    }
                    return json.dumps(solution)

# Solve the puzzle and print the result
print(solve_puzzle())