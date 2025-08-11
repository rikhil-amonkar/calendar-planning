import json
from itertools import permutations

def solve_puzzle():
    # Define all possible values for each category
    names = ['Eric', 'Alice', 'Peter', 'Bob', 'Arnold']
    children = ['Timothy', 'Meredith', 'Samantha', 'Fred', 'Bella']
    
    # Generate all possible permutations for names and children
    for name_perm in permutations(names):
        for child_perm in permutations(children):
            # Assign to houses 1-5
            assignment = []
            for i in range(5):
                assignment.append({
                    'House': str(i+1),
                    'Name': name_perm[i],
                    'Child': child_perm[i]
                })
            
            # Check all constraints
            valid = True
            
            # Constraint 3: Fred is in the second house
            if assignment[1]['Child'] != 'Fred':
                valid = False
                continue
            
            # Constraint 7: Fred is directly left of Bella
            if assignment[2]['Child'] != 'Bella':
                valid = False
                continue
            
            # Find Samantha's position
            samantha_pos = None
            for i, house in enumerate(assignment):
                if house['Child'] == 'Samantha':
                    samantha_pos = i
                    break
            if samantha_pos is None:
                valid = False
                continue
            
            # Constraint 1: Bob is left of Samantha
            bob_pos = None
            for i, house in enumerate(assignment):
                if house['Name'] == 'Bob':
                    bob_pos = i
                    break
            if bob_pos is None or bob_pos >= samantha_pos:
                valid = False
                continue
            
            # Constraint 2: Timothy's mother is left of Samantha
            timothy_pos = None
            for i, house in enumerate(assignment):
                if house['Child'] == 'Timothy':
                    timothy_pos = i
                    break
            if timothy_pos is None or timothy_pos >= samantha_pos:
                valid = False
                continue
            
            # Constraint 4: One house between Alice and Samantha
            alice_pos = None
            for i, house in enumerate(assignment):
                if house['Name'] == 'Alice':
                    alice_pos = i
                    break
            if alice_pos is None or abs(alice_pos - samantha_pos) != 2:
                valid = False
                continue
            
            # Constraint 5: Eric is not in the third house
            if assignment[2]['Name'] == 'Eric':
                valid = False
                continue
            
            # Constraint 6: Bob is not in the third house
            if assignment[2]['Name'] == 'Bob':
                valid = False
                continue
            
            # Constraint 8: Samantha is left of Peter
            peter_pos = None
            for i, house in enumerate(assignment):
                if house['Name'] == 'Peter':
                    peter_pos = i
                    break
            if peter_pos is None or samantha_pos >= peter_pos:
                valid = False
                continue
            
            if valid:
                # Prepare the solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Child"],
                        "rows": []
                    }
                }
                for house in assignment:
                    solution["solution"]["rows"].append([
                        house['House'],
                        house['Name'],
                        house['Child']
                    ])
                return solution
    
    return {"solution": {"header": [], "rows": []}}

# Solve and print the solution
solution = solve_puzzle()
print(json.dumps(solution, indent=2))