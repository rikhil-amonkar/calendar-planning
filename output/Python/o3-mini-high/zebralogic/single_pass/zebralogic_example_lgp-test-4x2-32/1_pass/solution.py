#!/usr/bin/env python3
import itertools
import json

def solve():
    houses = [1, 2, 3, 4]
    names = ["Peter", "Arnold", "Eric", "Alice"]
    pets = ["bird", "fish", "dog", "cat"]

    # Iterate over all possible arrangements of names and pets.
    for name_perm in itertools.permutations(names):
        # Clue 2: Eric is not in the first house.
        # Clue 5: Alice is not in the first house.
        if name_perm[0] in ["Eric", "Alice"]:
            continue
        for pet_perm in itertools.permutations(pets):
            valid = True
            # Clue 3: Eric is the person who keeps a pet bird.
            # Clue 6: Arnold is the person with an aquarium of fish.
            for i in range(4):
                if name_perm[i] == "Eric" and pet_perm[i] != "bird":
                    valid = False
                    break
                if name_perm[i] == "Arnold" and pet_perm[i] != "fish":
                    valid = False
                    break
            if not valid:
                continue

            # Clue 1: The person who owns a dog is somewhere to the right of Alice.
            alice_index = name_perm.index("Alice")
            dog_index = pet_perm.index("dog")
            if dog_index <= alice_index:
                continue

            # Clue 4: There is one house between the person with an aquarium of fish (Arnold) and Peter.
            arnold_index = name_perm.index("Arnold")
            peter_index = name_perm.index("Peter")
            if abs(arnold_index - peter_index) != 2:
                continue

            # All constraints satisfied, build the solution dictionary.
            solution = {
                "solution": {
                    "header": ["House", "Name", "Pet"],
                    "rows": []
                }
            }
            for i in range(4):
                # House numbers are string values as specified.
                solution["solution"]["rows"].append([str(i+1), name_perm[i], pet_perm[i]])
            return solution
    return None

if __name__ == "__main__":
    sol = solve()
    print(json.dumps(sol))