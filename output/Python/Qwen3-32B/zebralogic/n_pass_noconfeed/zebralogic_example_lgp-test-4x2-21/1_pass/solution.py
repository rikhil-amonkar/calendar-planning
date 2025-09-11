import itertools
import json

def main():
    names = ['Eric', 'Arnold', 'Alice', 'Peter']
    styles = ['craftsman', 'colonial', 'ranch', 'victorian']
    
    # Generate valid name permutations where house 2 (index 1) is Alice
    valid_name_perms = [p for p in itertools.permutations(names) if p[1] == 'Alice']
    
    # Generate valid style permutations where house 2 (index 1) is craftsman
    valid_style_perms = [p for p in itertools.permutations(styles) if p[1] == 'craftsman']
    
    solution_found = None
    
    for name_perm in valid_name_perms:
        for style_perm in valid_style_perms:
            # Check clue 2: Victorian directly left of Peter
            victorian_index = style_perm.index('victorian')
            if victorian_index + 1 >= 4:
                continue  # out of bounds
            if name_perm[victorian_index + 1] != 'Peter':
                continue
            
            # Check clue 3: Peter is to the right of ranch
            ranch_index = style_perm.index('ranch')
            peter_index = name_perm.index('Peter')
            if ranch_index >= peter_index:
                continue
            
            # Check clue 4: Arnold is to the right of Craftsman (house 2, index 1)
            arnold_index = name_perm.index('Arnold')
            if arnold_index <= 1:
                continue
            
            # All clues satisfied
            solution_found = list(zip([str(i+1) for i in range(4)], name_perm, style_perm))
            break
        if solution_found:
            break
    
    # Construct the JSON output
    output = {
        "solution": {
            "header": ["House", "Name", "HouseStyle"],
            "rows": []
        }
    }
    
    for row in solution_found:
        output['solution']['rows'].append(list(row))
    
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()