import itertools
import json

def solve_puzzle():
    names = ['Alice', 'Peter', 'Arnold', 'Eric']
    mothers = ['Holly', 'Kailyn', 'Janelle', 'Aniya']
    flowers = ['carnations', 'roses', 'lilies', 'daffodils']
    
    # Generate valid permutations for names, mothers, and flowers based on constraints
    valid_name_perms = []
    for p in itertools.permutations(names):
        if p[2] == 'Alice':  # Alice is in the third house
            valid_name_perms.append(p)
    
    valid_mother_perms = []
    for p in itertools.permutations(mothers):
        if p[2] == 'Kailyn':  # Kailyn is Alice's mother (third house)
            valid_mother_perms.append(p)
    
    valid_flower_perms = []
    for p in itertools.permutations(flowers):
        if p[1] == 'lilies':  # Lilies in the second house (directly left of Alice)
            valid_flower_perms.append(p)
    
    # Check all combinations of valid permutations
    for name_perm in valid_name_perms:
        arnold_idx = name_perm.index('Arnold')
        eric_idx = name_perm.index('Eric')
        peter_idx = name_perm.index('Peter')
        
        for mother_perm in valid_mother_perms:
            # Arnold's mother is Holly
            if mother_perm[arnold_idx] != 'Holly':
                continue
            
            for flower_perm in valid_flower_perms:
                # Eric loves daffodils
                if flower_perm[eric_idx] != 'daffodils':
                    continue
                
                # Find carnations position
                carnations_idx = flower_perm.index('carnations')
                
                # Carnations is to the right of Holly's (Arnold's) house
                if carnations_idx <= arnold_idx:
                    continue
                
                # Janelle is to the right of Arnold
                janelle_idx = mother_perm.index('Janelle')
                if janelle_idx <= arnold_idx:
                    continue
                
                # Peter is to the right of carnations lover
                if peter_idx <= carnations_idx:
                    continue
                
                # Construct solution
                solution_data = {
                    "solution": {
                        "header": ["House", "Name", "Mother", "Flower"],
                        "rows": []
                    }
                }
                for i in range(4):
                    house = str(i + 1)
                    name = name_perm[i]
                    mother = mother_perm[i]
                    flower = flower_perm[i]
                    solution_data["solution"]["rows"].append([house, name, mother, flower])
                
                print(json.dumps(solution_data))
                return

solve_puzzle()