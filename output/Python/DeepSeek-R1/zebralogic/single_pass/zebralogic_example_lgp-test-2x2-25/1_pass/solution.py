import itertools
import json

def main():
    names = ['Arnold', 'Eric']
    vacations = ['beach', 'mountain']
    
    name_perms = list(itertools.permutations(names))
    vac_perms = list(itertools.permutations(vacations))
    
    solution_found = None
    for n_perm in name_perms:
        for v_perm in vac_perms:
            candidate = {
                1: {'name': n_perm[0], 'vacation': v_perm[0]},
                2: {'name': n_perm[1], 'vacation': v_perm[1]}
            }
            arnold_house = None
            beach_house = None
            for house in [1, 2]:
                if candidate[house]['name'] == 'Arnold':
                    arnold_house = house
                if candidate[house]['vacation'] == 'beach':
                    beach_house = house
            if arnold_house is not None and beach_house is not None and arnold_house > beach_house:
                solution_found = candidate
                break
        if solution_found is not None:
            break
            
    if solution_found is None:
        solution_found = {1: {'name': 'Unknown', 'vacation': 'Unknown'}, 2: {'name': 'Unknown', 'vacation': 'Unknown'}}
    
    header = ["House", "name", "vacation"]
    rows = []
    for house_num in [1, 2]:
        row = [str(house_num), solution_found[house_num]['name'], solution_found[house_num]['vacation']]
        rows.append(row)
        
    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()