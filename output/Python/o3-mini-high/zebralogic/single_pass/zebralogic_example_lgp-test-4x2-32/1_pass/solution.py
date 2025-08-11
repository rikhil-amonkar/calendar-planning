#!/usr/bin/env python3
import itertools
import json

def main():
    names = ["Peter", "Arnold", "Eric", "Alice"]
    pets = ["bird", "fish", "dog", "cat"]
    
    solution = None
    # Houses are indexed 0 to 3 representing House 1 to House 4.
    for names_perm in itertools.permutations(names):
        # Constraint 5 and part of Constraint 2:
        # Alice and Eric are not in the first house.
        if names_perm[0] in ("Alice", "Eric"):
            continue
        
        for pets_perm in itertools.permutations(pets):
            # Build house assignments: house i gets (names_perm[i], pets_perm[i])
            # Constraint 6: Arnold is the person with an aquarium of fish.
            arnold_index = names_perm.index("Arnold")
            if pets_perm[arnold_index] != "fish":
                continue
            
            # Constraint 3: Eric is the person who keeps a pet bird.
            eric_index = names_perm.index("Eric")
            if pets_perm[eric_index] != "bird":
                continue
            
            # Constraint 2: Eric is not in the first house.
            if eric_index == 0:
                continue
            
            # Constraint 4: There is one house between the person with the aquarium of fish and Peter.
            # Fish is with Arnold.
            peter_index = names_perm.index("Peter")
            if abs(arnold_index - peter_index) != 2:
                continue
            
            # Constraint 1: The person who owns a dog is somewhere to the right of Alice.
            alice_index = names_perm.index("Alice")
            try:
                dog_index = pets_perm.index("dog")
            except ValueError:
                continue
            if dog_index <= alice_index:
                continue

            # All constraints satisfied, record the solution.
            houses = []
            for i in range(4):
                # House numbers as strings "1", "2", ...
                houses.append([str(i+1), names_perm[i], pets_perm[i]])
            solution = {
                "solution": {
                    "header": ["House", "Name", "Pet"],
                    "rows": houses
                }
            }
            break
        if solution is not None:
            break

    if solution is None:
        # In case no solution was found.
        solution = {"solution": {"header": ["House", "Name", "Pet"], "rows": []}}
    print(json.dumps(solution))

if __name__ == "__main__":
    main()