import itertools
import json

def main():
    # Define the attributes
    names = ['Alice', 'Arnold', 'Peter', 'Eric']
    hair_colors = ['black', 'blonde', 'brown', 'red']
    
    # Generate all permutations of names with house1 fixed to Alice
    other_names = [n for n in names if n != 'Alice']
    name_perms = list(itertools.permutations(other_names))
    
    # Generate all permutations of hair colors
    hair_perms = list(itertools.permutations(hair_colors))
    
    solution_found = None
    
    # Check all combinations
    for np in name_perms:
        full_names = ['Alice'] + list(np)
        for hp in hair_perms:
            full_hairs = list(hp)
            
            # Check constraints
            # Constraint 4: Black hair not in first house
            if full_hairs[0] == 'black':
                continue
                
            # Constraint 2: Alice and Arnold adjacent
            adjacent = False
            for i in range(3):
                if (full_names[i] == 'Alice' and full_names[i+1] == 'Arnold') or \
                   (full_names[i] == 'Arnold' and full_names[i+1] == 'Alice'):
                    adjacent = True
                    break
            if not adjacent:
                continue
                
            # Constraint 3: Eric has brown hair
            eric_has_brown = True
            for i in range(4):
                if full_names[i] == 'Eric' and full_hairs[i] != 'brown':
                    eric_has_brown = False
                    break
            if not eric_has_brown:
                continue
                
            # Constraint 1: Eric directly left of blonde hair
            eric_index = None
            for i in range(4):
                if full_names[i] == 'Eric':
                    eric_index = i
                    break
            if eric_index is None or eric_index == 3 or full_hairs[eric_index+1] != 'blonde':
                continue
                
            # All constraints satisfied
            solution_found = (full_names, full_hairs)
            break
            
        if solution_found:
            break
            
    # Format the solution
    if solution_found:
        full_names, full_hairs = solution_found
        rows = []
        for i in range(4):
            rows.append([str(i+1), full_names[i], full_hairs[i]])
        
        result = {
            "solution": {
                "header": ["House", "Name", "HairColor"],
                "rows": rows
            }
        }
        print(json.dumps(result))
    else:
        # Should not happen for this puzzle
        print('{"solution": {}}')

if __name__ == "__main__":
    main()