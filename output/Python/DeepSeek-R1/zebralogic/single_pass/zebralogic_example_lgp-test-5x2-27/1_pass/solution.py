import itertools
import json

def main():
    # Define fixed constraints
    fixed_name_positions = {3: 'Alice'}
    fixed_height_positions = {1: 'short', 4: 'average'}
    
    # Free positions and values
    free_name_positions = [0, 1, 2, 4]
    free_names = ['Peter', 'Bob', 'Eric', 'Arnold']
    free_height_positions = [0, 2, 3]
    free_heights = ['very tall', 'tall', 'very short']
    
    found = False
    solution_names = None
    solution_heights = None
    
    for name_perm in itertools.permutations(free_names):
        names = [None] * 5
        for idx, val in fixed_name_positions.items():
            names[idx] = val
        for idx, pos in enumerate(free_name_positions):
            names[pos] = name_perm[idx]
        
        # Check clue 2: Peter is directly left of Bob
        try:
            peter_index = names.index('Peter')
        except ValueError:
            continue
        if peter_index >= 4:
            continue
        if names[peter_index + 1] != 'Bob':
            continue
        
        # Check clue 3: Eric is left of Peter
        try:
            eric_index = names.index('Eric')
        except ValueError:
            continue
        if eric_index >= peter_index:
            continue
        
        for height_perm in itertools.permutations(free_heights):
            heights = [None] * 5
            for idx, val in fixed_height_positions.items():
                heights[idx] = val
            for idx, pos in enumerate(free_height_positions):
                heights[pos] = height_perm[idx]
            
            # Check clue 4: Very tall is directly left of Peter
            if peter_index == 0:
                continue
            if heights[peter_index - 1] != 'very tall':
                continue
            
            # Check clue 6: Short and very short are adjacent
            try:
                very_short_index = heights.index('very short')
            except ValueError:
                continue
            if abs(very_short_index - 1) != 1:
                continue
            
            solution_names = names
            solution_heights = heights
            found = True
            break
        
        if found:
            break
    
    if not found:
        result = {"error": "No solution found"}
    else:
        rows = []
        for i in range(5):
            rows.append([str(i + 1), solution_names[i], solution_heights[i]])
        result = {
            "solution": {
                "header": ["House", "Name", "Height"],
                "rows": rows
            }
        }
    
    print(json.dumps(result))

if __name__ == '__main__':
    main()