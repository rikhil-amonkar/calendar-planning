import itertools
import json

# Define the fixed positions for names
fixed_names = {
    1: 'Peter',
    3: 'Bob',
    5: 'Carol',
    6: 'Eric'
}

# Define the remaining names to assign (for houses 2 and 4)
remaining_names = ['Arnold', 'Alice']

# Define the fixed positions for cigars
fixed_cigars = {
    3: 'pall mall',
    5: 'blue master'
}

# Define the remaining cigars to assign (for houses 1, 2, 4, 6)
remaining_cigar_list = ['blends', 'yellow monster', 'dunhill', 'prince']
remaining_cigar_positions = [1, 2, 4, 6]

# Iterate through possible name assignments for houses 2 and 4
for name_2, name_4 in itertools.permutations(remaining_names):
    names = [None] * 7  # indexes 0-6, 0 unused
    names[1] = fixed_names[1]
    names[3] = fixed_names[3]
    names[5] = fixed_names[5]
    names[6] = fixed_names[6]
    names[2] = name_2
    names[4] = name_4
    
    # Now generate all possible permutations for the remaining cigars
    for cigar_perm in itertools.permutations(remaining_cigar_list):
        # Assign the cigars to the remaining positions
        temp_cigars = [None] * 7  # indexes 0-6
        temp_cigars[3] = fixed_cigars[3]
        temp_cigars[5] = fixed_cigars[5]
        for idx, pos in enumerate(remaining_cigar_positions):
            temp_cigars[pos] = cigar_perm[idx]
        
        # Check clue 4: one house between Yellow Monster and Blends
        ym_pos = None
        blends_pos = None
        for pos in remaining_cigar_positions:
            if temp_cigars[pos] == 'yellow monster':
                ym_pos = pos
            if temp_cigars[pos] == 'blends':
                blends_pos = pos
        
        if ym_pos is None or blends_pos is None:
            continue  # Shouldn't happen as they are in remaining_cigar_list
        
        if abs(ym_pos - blends_pos) != 2:
            continue
        
        # Check clue 1: Arnold is to the left of blends
        arnold_house = 2 if names[2] == 'Arnold' else (4 if names[4] == 'Arnold' else None)
        if arnold_house >= blends_pos:
            continue
        
        # Check clue 3: Arnold is to the left of Prince
        prince_pos = None
        for pos in remaining_cigar_positions:
            if temp_cigars[pos] == 'prince':
                prince_pos = pos
                break
        if prince_pos is None:
            continue  # Shouldn't happen
        
        if arnold_house >= prince_pos:
            continue
        
        # All constraints are satisfied. Build the solution.
        solution_rows = []
        for house in range(1, 7):
            solution_rows.append([
                str(house),
                names[house],
                temp_cigars[house]
            ])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Cigar"],
                "rows": solution_rows
            }
        }
        
        # Output as JSON
        print(json.dumps(solution, indent=2))
        exit()  # Exit after finding the first solution