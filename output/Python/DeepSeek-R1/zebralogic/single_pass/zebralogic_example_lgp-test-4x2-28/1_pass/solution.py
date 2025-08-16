import itertools
import json

def main():
    # Define the attributes
    names_all = ['Alice', 'Arnold', 'Peter', 'Eric']
    hair_colors_all = ['black', 'blonde', 'brown', 'red']
    
    # Generate name assignments: house0 is Alice, house1 is Arnold, and the last two houses are permutations of Peter and Eric.
    name_assignments = [
        ['Alice', 'Arnold', 'Eric', 'Peter'],
        ['Alice', 'Arnold', 'Peter', 'Eric']
    ]
    
    # Generate all hair color permutations and filter out those with black in house0 (index0)
    hair_perms = list(itertools.permutations(hair_colors_all))
    valid_hair_perms = [perm for perm in hair_perms if perm[0] != 'black']
    
    solution = None
    
    for names in name_assignments:
        for hair in valid_hair_perms:
            eric_index = names.index('Eric')
            # Check Eric has brown hair
            if hair[eric_index] != 'brown':
                continue
            # Check Eric is not in the last house and the next house has blonde hair
            if eric_index < 3:
                if hair[eric_index + 1] == 'blonde':
                    solution = (names, hair)
                    break
        if solution:
            break
    
    if solution:
        names_sol, hair_sol = solution
        rows = []
        for i in range(4):
            house_num = str(i + 1)
            row = [house_num, names_sol[i], hair_sol[i]]
            rows.append(row)
        
        result = {
            "solution": {
                "header": ["House", "Name", "HairColor"],
                "rows": rows
            }
        }
        print(json.dumps(result))
    else:
        result = {
            "solution": {
                "header": ["House", "Name", "HairColor"],
                "rows": []
            }
        }
        print(json.dumps(result))

if __name__ == "__main__":
    main()