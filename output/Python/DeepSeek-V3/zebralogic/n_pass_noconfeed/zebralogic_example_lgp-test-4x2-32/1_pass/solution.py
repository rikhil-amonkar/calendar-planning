import json
from itertools import permutations

def solve_puzzle():
    names = ['Peter', 'Arnold', 'Eric', 'Alice']
    pets = ['bird', 'fish', 'dog', 'cat']
    houses = [1, 2, 3, 4]
    
    # Generate all possible permutations of names and pets
    for name_perm in permutations(names):
        for pet_perm in permutations(pets):
            assignment = list(zip(name_perm, pet_perm))
            
            # Check clue 2: Eric is not in the first house
            if assignment[0][0] == 'Eric':
                continue
                
            # Check clue 5: Alice is not in the first house
            if assignment[0][0] == 'Alice':
                continue
                
            # Check clue 3: Eric is the person who keeps a pet bird
            eric_index = None
            for i, (name, pet) in enumerate(assignment):
                if name == 'Eric':
                    eric_index = i
                    if pet != 'bird':
                        break
            else:
                if eric_index is None:
                    continue
                # Check clue 1: The person who owns a dog is somewhere to the right of Alice
                alice_index = None
                dog_index = None
                for i, (name, pet) in enumerate(assignment):
                    if name == 'Alice':
                        alice_index = i
                    if pet == 'dog':
                        dog_index = i
                if alice_index is None or dog_index is None or dog_index <= alice_index:
                    continue
                    
                # Check clue 6: Arnold is the person with an aquarium of fish
                arnold_index = None
                fish_index = None
                for i, (name, pet) in enumerate(assignment):
                    if name == 'Arnold':
                        arnold_index = i
                    if pet == 'fish':
                        fish_index = i
                if arnold_index != fish_index:
                    continue
                    
                # Check clue 4: There is one house between the person with an aquarium of fish and Peter
                peter_index = None
                for i, (name, pet) in enumerate(assignment):
                    if name == 'Peter':
                        peter_index = i
                if abs(fish_index - peter_index) != 2:
                    continue
                    
                # If all clues are satisfied, return the solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Pet"],
                        "rows": []
                    }
                }
                for i, (name, pet) in enumerate(assignment):
                    solution["solution"]["rows"].append([str(i+1), name, pet])
                return solution
                
    return None

def main():
    solution = solve_puzzle()
    if solution:
        print(json.dumps(solution, indent=2))
    else:
        print(json.dumps({"solution": {"header": ["House", "Name", "Pet"], "rows": []}}, indent=2))

if __name__ == "__main__":
    main()