import itertools
import json

def main():
    # Define the fixed attributes
    names = ['Peter', None, None, None]  # House 1: Peter
    colors = [None, None, 'green', None] # House 3: green

    # Remaining names and colors
    remaining_names = ['Arnold', 'Alice', 'Eric']
    remaining_colors = ['yellow', 'red', 'white']

    # Generate permutations for names (positions 1,2,3) and colors (positions 0,1,3)
    for name_perm in itertools.permutations(remaining_names):
        candidate_names = names.copy()
        candidate_names[1] = name_perm[0]  # House 2
        candidate_names[2] = name_perm[1]  # House 3
        candidate_names[3] = name_perm[2]  # House 4

        for color_perm in itertools.permutations(remaining_colors):
            candidate_colors = colors.copy()
            candidate_colors[0] = color_perm[0]  # House 1
            candidate_colors[1] = color_perm[1]  # House 2
            candidate_colors[3] = color_perm[2]  # House 4

            # Constraint 5: Eric loves yellow
            eric_index = candidate_names.index('Eric')
            if candidate_colors[eric_index] != 'yellow':
                continue

            # Constraint 4: Arnold directly left of Eric
            if eric_index == 0 or candidate_names[eric_index-1] != 'Arnold':
                continue

            # Constraint 3: One house between red and yellow
            yellow_index = candidate_colors.index('yellow')
            red_index = candidate_colors.index('red')
            if abs(red_index - yellow_index) != 2:
                continue

            # Build the solution
            solution_rows = []
            for i in range(4):
                solution_rows.append([str(i+1), candidate_names[i], candidate_colors[i]])
            
            solution = {
                "header": ["House", "Name", "Color"],
                "rows": solution_rows
            }
            
            # Output the solution as JSON
            print(json.dumps({"solution": solution}, indent=None))
            return
    
    # If no solution found
    print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()