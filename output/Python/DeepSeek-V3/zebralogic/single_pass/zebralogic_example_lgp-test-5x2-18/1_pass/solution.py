import json
from itertools import permutations

def solve_puzzle():
    # Define the possible values for each attribute
    names = ['Eric', 'Alice', 'Peter', 'Bob', 'Arnold']
    children = ['Timothy', 'Meredith', 'Samantha', 'Fred', 'Bella']
    
    # Generate all possible permutations for names and children
    for name_perm in permutations(names):
        for child_perm in permutations(children):
            # Assign to houses 1-5
            assignment = [
                {'House': str(i+1), 'Name': name_perm[i], 'Children': child_perm[i]}
                for i in range(5)
            ]
            
            # Check all constraints
            # Constraint 3: Fred is in the second house
            if assignment[1]['Children'] != 'Fred':
                continue
            
            # Constraint 7: Fred is directly left of Bella
            if assignment[2]['Children'] != 'Bella':
                continue
            
            # Constraint 4: One house between Alice and Samantha
            alice_indices = [i for i, h in enumerate(assignment) if h['Name'] == 'Alice']
            samantha_indices = [i for i, h in enumerate(assignment) if h['Children'] == 'Samantha']
            if not alice_indices or not samantha_indices:
                continue
            alice_pos = alice_indices[0]
            samantha_pos = samantha_indices[0]
            if samantha_pos - alice_pos != 2:
                continue
            
            # Constraint 1: Bob is left of Samantha
            bob_indices = [i for i, h in enumerate(assignment) if h['Name'] == 'Bob']
            if not bob_indices:
                continue
            bob_pos = bob_indices[0]
            if bob_pos >= samantha_pos:
                continue
            
            # Constraint 2: Timothy's mother is left of Samantha
            timothy_indices = [i for i, h in enumerate(assignment) if h['Children'] == 'Timothy']
            if not timothy_indices:
                continue
            timothy_pos = timothy_indices[0]
            if timothy_pos >= samantha_pos:
                continue
            
            # Constraint 5: Eric is not in the third house
            if assignment[2]['Name'] == 'Eric':
                continue
            
            # Constraint 6: Bob is not in the third house
            if assignment[2]['Name'] == 'Bob':
                continue
            
            # Constraint 8: Samantha is left of Peter
            peter_indices = [i for i, h in enumerate(assignment) if h['Name'] == 'Peter']
            if not peter_indices:
                continue
            peter_pos = peter_indices[0]
            if samantha_pos >= peter_pos:
                continue
            
            # If all constraints are satisfied, return the solution
            solution = {
                "solution": {
                    "header": ["House", "Name", "Children"],
                    "rows": [
                        [h['House'], h['Name'], h['Children']]
                        for h in assignment
                    ]
                }
            }
            return solution
    
    return {"solution": {"header": ["House", "Name", "Children"], "rows": []}}

# Solve the puzzle and print the solution as JSON
print(json.dumps(solve_puzzle()))