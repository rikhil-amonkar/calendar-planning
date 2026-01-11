import json
from itertools import permutations

def solve_puzzle():
    names = ["Peter", "Arnold", "Eric", "Alice"]
    pets = ["bird", "fish", "dog", "cat"]
    houses = [1, 2, 3, 4]
    
    # Generate all possible permutations of names and pets
    for name_perm in permutations(names, 4):
        for pet_perm in permutations(pets, 4):
            # Create assignment
            assignment = {}
            for i in range(4):
                assignment[houses[i]] = {
                    "Name": name_perm[i],
                    "Pet": pet_perm[i]
                }
            
            # Check clues
            # 1. Dog owner is somewhere to the right of Alice
            alice_house = None
            dog_house = None
            for house in houses:
                if assignment[house]["Name"] == "Alice":
                    alice_house = house
                if assignment[house]["Pet"] == "dog":
                    dog_house = house
            if not (alice_house is not None and dog_house is not None and dog_house > alice_house):
                continue
            
            # 2. Eric is not in the first house
            if assignment[1]["Name"] == "Eric":
                continue
            
            # 3. Eric keeps a pet bird
            eric_house = None
            for house in houses:
                if assignment[house]["Name"] == "Eric":
                    eric_house = house
                    break
            if eric_house is None or assignment[eric_house]["Pet"] != "bird":
                continue
            
            # 4. One house between fish and Peter
            fish_house = None
            peter_house = None
            for house in houses:
                if assignment[house]["Pet"] == "fish":
                    fish_house = house
                if assignment[house]["Name"] == "Peter":
                    peter_house = house
            if not (fish_house is not None and peter_house is not None and abs(fish_house - peter_house) == 2):
                continue
            
            # 5. Alice is not in the first house
            if assignment[1]["Name"] == "Alice":
                continue
            
            # 6. Arnold is the person with fish
            arnold_house = None
            for house in houses:
                if assignment[house]["Name"] == "Arnold":
                    arnold_house = house
                    break
            if arnold_house is None or assignment[arnold_house]["Pet"] != "fish":
                continue
            
            # All clues satisfied - format solution
            rows = []
            for house in houses:
                rows.append([str(house), assignment[house]["Name"], assignment[house]["Pet"]])
            
            return {
                "solution": {
                    "header": ["House", "Name", "Pet"],
                    "rows": rows
                }
            }
    
    return None

def main():
    solution = solve_puzzle()
    if solution:
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"error": "No solution found"}, indent=2))

if __name__ == "__main__":
    main()