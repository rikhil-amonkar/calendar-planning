import itertools
import json

def solve_puzzle():
    names = ['Eric', 'Alice', 'Peter', 'Bob', 'Arnold']
    children = ['Timothy', 'Meredith', 'Samantha', 'Fred', 'Bella']
    
    for name_perm in itertools.permutations(names):
        # Skip if Eric or Bob is in the third house
        if name_perm[2] == 'Eric' or name_perm[2] == 'Bob':
            continue
        
        for child_perm in itertools.permutations(children):
            # Check clue 3 and 7: Fred in house 2, Bella directly to the right
            if child_perm[1] != 'Fred' or child_perm[2] != 'Bella':
                continue
            
            # Find indices for Samantha, Timothy, etc.
            try:
                s_index = child_perm.index('Samantha')
                t_index = child_perm.index('Timothy')
                p_index = name_perm.index('Peter')
                a_index = name_perm.index('Alice')
                b_index = name_perm.index('Bob')
            except ValueError:
                continue  # Should not happen with permutations
            
            # Clue 8: Samantha is left of Peter
            if not (s_index < p_index):
                continue
            
            # Clue 1: Bob left of Samantha
            if not (b_index < s_index):
                continue
            
            # Clue 2: Timothy's mother left of Samantha
            if not (t_index < s_index):
                continue
            
            # Clue 4: Alice and Samantha have one house between
            if abs(a_index - s_index) != 2:
                continue
            
            # All constraints satisfied; build the solution
            solution_data = {
                "solution": {
                    "header": ["House", "Name", "Children"],
                    "rows": []
                }
            }
            for i in range(5):
                house_num = str(i + 1)
                name = name_perm[i]
                child = child_perm[i]
                solution_data["solution"]["rows"].append([house_num, name, child])
            
            return json.dumps(solution_data)
    
    return None  # If no solution found

# Execute and print the JSON result
print(solve_puzzle())