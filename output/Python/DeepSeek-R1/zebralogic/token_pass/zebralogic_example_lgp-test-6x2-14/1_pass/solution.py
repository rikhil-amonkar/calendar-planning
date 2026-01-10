import itertools
import json

def main():
    # Initialize the houses
    n_houses = 6
    names = [None] * n_houses
    cigars = [None] * n_houses

    # Fixed assignments from clues
    names[0] = 'Peter'    # House 1
    names[2] = 'Bob'      # House 3
    names[4] = 'Carol'    # House 5
    names[5] = 'Eric'     # House 6

    cigars[2] = 'pall mall'   # House 3
    cigars[4] = 'blue master' # House 5

    # Determine indices for unknown attributes
    unknown_name_indices = [1, 3]   # Houses 2 and 4
    unknown_cigar_indices = [0, 1, 3, 5]  # Houses 1, 2, 4, 6

    available_names = ['Arnold', 'Alice']
    available_cigars = ['blends', 'yellow monster', 'dunhill', 'prince']

    # Iterate over all permutations of names and cigars
    for name_perm in itertools.permutations(available_names):
        # Assign names to unknown indices
        for idx, name in zip(unknown_name_indices, name_perm):
            names[idx] = name
        
        for cigar_perm in itertools.permutations(available_cigars):
            # Assign cigars to unknown indices
            for idx, cigar in zip(unknown_cigar_indices, cigar_perm):
                cigars[idx] = cigar
            
            # Find indices for constraint checks
            arnold_index = None
            blends_index = None
            prince_index = None
            ym_index = None
            
            for i in range(n_houses):
                if names[i] == 'Arnold':
                    arnold_index = i
                if cigars[i] == 'blends':
                    blends_index = i
                if cigars[i] == 'prince':
                    prince_index = i
                if cigars[i] == 'yellow monster':
                    ym_index = i
            
            # Check constraints
            if arnold_index is None or blends_index is None or prince_index is None or ym_index is None:
                continue
            
            # Clue 1: Arnold left of blends smoker
            if arnold_index >= blends_index:
                continue
            
            # Clue 3: Arnold left of prince smoker
            if arnold_index >= prince_index:
                continue
            
            # Clue 4: One house between Yellow Monster and blends
            if abs(ym_index - blends_index) != 2:
                continue
            
            # All constraints satisfied, prepare solution
            solution_rows = []
            for i in range(n_houses):
                solution_rows.append([str(i+1), names[i], cigars[i]])
            
            result = {
                "solution": {
                    "header": ["House", "Name", "Cigar"],
                    "rows": solution_rows
                }
            }
            
            print(json.dumps(result, indent=2))
            return
    
    # If no solution found
    print('{"solution": {"header": ["House", "Name", "Cigar"], "rows": []}}')

if __name__ == "__main__":
    main()