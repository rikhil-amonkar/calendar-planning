import itertools
import json

def main():
    names = ['Peter', 'Arnold', 'Eric', 'Alice']
    pets = ['bird', 'fish', 'dog', 'cat']
    
    solution_found = False
    sol_names = None
    sol_pets = None
    
    for name_perm in itertools.permutations(names):
        # Constraint 2: Eric not in first house
        # Constraint 5: Alice not in first house
        if name_perm[0] == 'Eric' or name_perm[0] == 'Alice':
            continue
            
        for pet_perm in itertools.permutations(pets):
            # Get indices for key persons
            eric_idx = name_perm.index('Eric')
            arnold_idx = name_perm.index('Arnold')
            alice_idx = name_perm.index('Alice')
            
            # Constraint 3: Eric has bird
            if pet_perm[eric_idx] != 'bird':
                continue
                
            # Constraint 6: Arnold has fish
            if pet_perm[arnold_idx] != 'fish':
                continue
                
            # Constraint 1: Dog owner is right of Alice
            dog_idx = pet_perm.index('dog')
            if dog_idx <= alice_idx:
                continue
                
            # Constraint 4: One house between fish (Arnold) and Peter
            peter_idx = name_perm.index('Peter')
            if abs(arnold_idx - peter_idx) != 2:
                continue
                
            # All constraints satisfied
            sol_names = name_perm
            sol_pets = pet_perm
            solution_found = True
            break
            
        if solution_found:
            break
            
    if not solution_found:
        print("No solution found")
        return
        
    # Prepare output structure
    rows = []
    for i in range(4):
        house_num = str(i+1)
        rows.append([house_num, sol_names[i], sol_pets[i]])
        
    result = {
        "solution": {
            "header": ["House", "Name", "Pet"],
            "rows": rows
        }
    }
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()