import itertools
import json

def main():
    # Define attributes and their domains
    names = ['Eric', 'Arnold', 'Peter']
    heights = ['very short', 'short', 'average']
    
    # Generate all permutations for names and heights
    all_name_perms = list(itertools.permutations(names))
    all_height_perms = list(itertools.permutations(heights))
    
    solution_found = None
    
    # Iterate over all combinations of name and height permutations
    for name_perm in all_name_perms:
        for height_perm in all_height_perms:
            candidate_names = list(name_perm)
            candidate_heights = list(height_perm)
            
            # Clue 1: Eric not in first house
            if candidate_names[0] == 'Eric':
                continue
                
            # Clue 4: Arnold not in first house
            if candidate_names[0] == 'Arnold':
                continue
                
            # Find index of 'very short' (Clue 3)
            try:
                idx_very_short = candidate_heights.index('very short')
            except ValueError:
                continue
                
            # Clue 3: Very short person is Eric
            if candidate_names[idx_very_short] != 'Eric':
                continue
                
            # Find index of 'short' (Clue 2)
            try:
                idx_short = candidate_heights.index('short')
            except ValueError:
                continue
                
            # Clue 2: Very short is left of short
            if idx_very_short >= idx_short:
                continue
                
            # Valid solution found
            solution_found = (candidate_names, candidate_heights)
            break
            
        if solution_found is not None:
            break
            
    if solution_found is None:
        print(json.dumps({"solution": {}}))
        return
        
    # Prepare the solution in required JSON format
    header = ["House", "Name", "Height"]
    rows = []
    for i in range(3):
        house_num = str(i+1)
        name_val = solution_found[0][i]
        height_val = solution_found[1][i]
        rows.append([house_num, name_val, height_val])
        
    result = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()