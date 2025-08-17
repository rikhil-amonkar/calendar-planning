import itertools
import json

names = ['Alice', 'Peter', 'Arnold', 'Eric']
mothers = ['Holly', 'Kailyn', 'Janelle', 'Aniya']
flowers = ['carnations', 'roses', 'lilies', 'daffodils']

solution = None

for name_perm in itertools.permutations(names):
    if name_perm[2] != 'Alice':
        continue
    
    for mother_perm in itertools.permutations(mothers):
        if mother_perm[2] != 'Kailyn':
            continue
        
        for flower_perm in itertools.permutations(flowers):
            if flower_perm[1] != 'lilies':
                continue
            
            # Check Eric's flower is daffodils
            eric_pos = name_perm.index('Eric')
            if flower_perm[eric_pos] != 'daffodils':
                continue
            
            # Check Arnold's mother is Holly
            arnold_pos = name_perm.index('Arnold')
            if mother_perm[arnold_pos] != 'Holly':
                continue
            
            # Check Janelle's position is to the right of Arnold
            janelle_pos = mother_perm.index('Janelle')
            if arnold_pos >= janelle_pos:
                continue
            
            # Check Peter is to the right of carnations lover
            carnations_pos = flower_perm.index('carnations')
            peter_pos = name_perm.index('Peter')
            if carnations_pos >= peter_pos:
                continue
            
            # Check carnations lover is to the right of Holly (Arnold's mother)
            if carnations_pos <= arnold_pos:
                continue
            
            # All constraints satisfied
            solution = {
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
                solution["solution"]["rows"].append([house, name, mother, flower])
            break  # Exit flower_perm loop
        if solution:
            break  # Exit mother_perm loop
    if solution:
        break  # Exit name_perm loop

print(json.dumps(solution, indent=2))