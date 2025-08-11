from itertools import permutations
import json

def main():
    names = ['Peter', 'Arnold', 'Eric']
    occupations = ['doctor', 'teacher', 'engineer']
    hobbies = ['cooking', 'photography', 'gardening']
    
    solution_found = None
    
    for name_perm in permutations(names):
        for occ_perm in permutations(occupations):
            for hob_perm in permutations(hobbies):
                houses = [
                    [name_perm[0], occ_perm[0], hob_perm[0]],
                    [name_perm[1], occ_perm[1], hob_perm[1]],
                    [name_perm[2], occ_perm[2], hob_perm[2]]
                ]
                
                # Find indices for key attributes
                try:
                    idx_doc = next(i for i in range(3) if houses[i][1] == 'doctor')
                    idx_eric = next(i for i in range(3) if houses[i][0] == 'Eric')
                    idx_cooking = next(i for i in range(3) if houses[i][2] == 'cooking')
                    idx_gardening = next(i for i in range(3) if houses[i][2] == 'gardening')
                    idx_photo = next(i for i in range(3) if houses[i][2] == 'photography')
                    idx_engineer = next(i for i in range(3) if houses[i][1] == 'engineer')
                except StopIteration:
                    continue
                
                # Constraint 1: Doctor and Eric are adjacent
                if abs(idx_doc - idx_eric) != 1:
                    continue
                    
                # Constraint 2: Cooking directly left of teacher
                if idx_cooking >= 2 or houses[idx_cooking+1][1] != 'teacher':
                    continue
                    
                # Constraint 3: Doctor right of gardening
                if idx_doc <= idx_gardening:
                    continue
                    
                # Constraint 4: Photography and teacher same house
                if houses[idx_photo][1] != 'teacher':
                    continue
                    
                # Constraint 5: Engineer and Peter same house
                if houses[idx_engineer][0] != 'Peter':
                    continue
                    
                # Valid solution found
                solution_found = houses
                break
            if solution_found:
                break
        if solution_found:
            break
            
    if solution_found:
        result = {
            "solution": {
                "header": ["House", "Name", "Occupation", "Hobby"],
                "rows": [
                    ["1", solution_found[0][0], solution_found[0][1], solution_found[0][2]],
                    ["2", solution_found[1][0], solution_found[1][1], solution_found[1][2]],
                    ["3", solution_found[2][0], solution_found[2][1], solution_found[2][2]]
                ]
            }
        }
    else:
        result = {"solution": {}}
        
    print(json.dumps(result))

if __name__ == "__main__":
    main()