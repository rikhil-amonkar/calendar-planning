import itertools
import json

def check_constraints(names, cigars):
    try:
        i_arnold = names.index('Arnold')
    except ValueError:
        return False
        
    try:
        i_blends = cigars.index('blends')
    except ValueError:
        return False
        
    if i_arnold >= i_blends:
        return False
        
    try:
        i_prince = cigars.index('prince')
    except ValueError:
        return False
        
    if i_arnold >= i_prince:
        return False
        
    try:
        i_yellow = cigars.index('yellow monster')
    except ValueError:
        return False
        
    if abs(i_yellow - i_blends) != 2:
        return False
        
    return True

def main():
    names = ['Peter', None, 'Bob', None, 'Carol', 'Eric']
    cigars = [None, None, 'pall mall', None, 'blue master', None]
    
    remaining_names = ['Arnold', 'Alice']
    remaining_cigars = ['blends', 'yellow monster', 'dunhill', 'prince']
    
    solution_names = None
    solution_cigars = None
    found = False
    
    for name_perm in itertools.permutations(remaining_names):
        candidate_names = names.copy()
        candidate_names[1] = name_perm[0]
        candidate_names[3] = name_perm[1]
        
        for cigar_perm in itertools.permutations(remaining_cigars):
            candidate_cigars = cigars.copy()
            candidate_cigars[0] = cigar_perm[0]
            candidate_cigars[1] = cigar_perm[1]
            candidate_cigars[3] = cigar_perm[2]
            candidate_cigars[5] = cigar_perm[3]
            
            if check_constraints(candidate_names, candidate_cigars):
                solution_names = candidate_names
                solution_cigars = candidate_cigars
                found = True
                break
        if found:
            break
            
    if found:
        rows = []
        for i in range(6):
            house = str(i+1)
            name = solution_names[i]
            cigar = solution_cigars[i]
            rows.append([house, name, cigar])
        solution_dict = {"solution": {"header": ["House", "Name", "Cigar"], "rows": rows}}
        print(json.dumps(solution_dict))
    else:
        rows = []
        for i in range(6):
            rows.append([str(i+1), "?", "?"])
        solution_dict = {"solution": {"header": ["House", "Name", "Cigar"], "rows": rows}}
        print(json.dumps(solution_dict))

if __name__ == "__main__":
    main()