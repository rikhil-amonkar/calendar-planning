import itertools
import json

def main():
    names = ["Peter", "Arnold", "Eric", "Alice"]
    pets = ["bird", "fish", "dog", "cat"]
    
    solution_found = None

    for name_perm in itertools.permutations(names):
        # Constraint 2 and 5: Eric and Alice cannot be in the first house.
        if name_perm[0] in ("Eric", "Alice"):
            continue
        
        for pet_perm in itertools.permutations(pets):
            # Constraint 3: Eric is the person who keeps a pet bird.
            if pet_perm[name_perm.index("Eric")] != "bird":
                continue
            # Constraint 6: Arnold is the person with an aquarium of fish.
            if pet_perm[name_perm.index("Arnold")] != "fish":
                continue
            # Constraint 1: The person who owns a dog is somewhere to the right of Alice.
            if pet_perm.index("dog") <= name_perm.index("Alice"):
                continue
            # Constraint 4: There is one house between the person with an aquarium of fish and Peter.
            # Since Arnold is the fish keeper, the absolute difference between Peter and Arnold must be 2.
            if abs(name_perm.index("Peter") - name_perm.index("Arnold")) != 2:
                continue
            
            # All constraints satisfied, record the solution.
            solution_found = [[str(i+1), name_perm[i], pet_perm[i]] for i in range(4)]
            break
        if solution_found is not None:
            break

    if solution_found is not None:
        output = {
            "solution": {
                "header": ["House", "Name", "Pet"],
                "rows": solution_found
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"solution": None}))

if __name__ == "__main__":
    main()