import itertools
import json

def main():
    # Define the attributes and houses
    names = ['Eric', 'Arnold', 'Alice', 'Peter']
    styles = ['craftsman', 'colonial', 'ranch', 'victorian']
    houses = [0, 1, 2, 3]  # 0-indexed: house1=0, house2=1, house3=2, house4=3
    
    # Fixed assignments from clues 1 and 5
    fixed_house_index = 1  # house2 is at index1 (0-indexed)
    fixed_name = 'Alice'
    fixed_style = 'craftsman'
    
    # Remaining names and styles for the other houses (house1, house3, house4)
    remaining_names = [n for n in names if n != fixed_name]
    remaining_styles = [s for s in styles if s != fixed_style]
    
    # Initialize solution arrays
    sol_names = [None] * 4
    sol_styles = [None] * 4
    
    # Set fixed house
    sol_names[fixed_house_index] = fixed_name
    sol_styles[fixed_house_index] = fixed_style
    
    # Generate permutations for remaining names and styles
    name_perms = list(itertools.permutations(remaining_names))
    style_perms = list(itertools.permutations(remaining_styles))
    
    solution_found = False
    
    for name_perm in name_perms:
        # Assign names to houses 1, 3, 4 (indices 0, 2, 3)
        sol_names[0] = name_perm[0]
        sol_names[2] = name_perm[1]
        sol_names[3] = name_perm[2]
        
        for style_perm in style_perms:
            # Assign styles to houses 1, 3, 4 (indices 0, 2, 3)
            sol_styles[0] = style_perm[0]
            sol_styles[2] = style_perm[1]
            sol_styles[3] = style_perm[2]
            
            # Check clue 2: Victorian directly left of Peter
            try:
                victorian_index = sol_styles.index('victorian')
            except ValueError:
                continue
                
            if victorian_index == 3:  # last house, no house to the right
                continue
            if sol_names[victorian_index + 1] != 'Peter':
                continue
                
            # Check clue 3: Peter right of ranch
            try:
                ranch_index = sol_styles.index('ranch')
                peter_index = sol_names.index('Peter')
            except ValueError:
                continue
                
            if ranch_index >= peter_index:
                continue
                
            # Check clue 4: Arnold right of Craftsman (which is at index1)
            try:
                arnold_index = sol_names.index('Arnold')
            except ValueError:
                continue
                
            if arnold_index <= 1:  # Craftsman is at index1, so Arnold must be > index1
                continue
                
            # All constraints satisfied
            solution_found = True
            break
            
        if solution_found:
            break
            
    if not solution_found:
        # Fallback in case no solution found (should not happen for this puzzle)
        print(json.dumps({"solution": {}}))
        return
        
    # Build the output structure
    header = ["House", "Name", "Style"]
    rows = []
    for i in range(4):
        house_num = str(i + 1)
        row = [house_num, sol_names[i], sol_styles[i]]
        rows.append(row)
        
    output = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    
    print(json.dumps(output))

if __name__ == "__main__":
    main()