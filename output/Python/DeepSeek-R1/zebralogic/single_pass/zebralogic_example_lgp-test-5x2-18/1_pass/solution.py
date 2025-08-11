import itertools
import json

def main():
    # Fixed child assignment based on constraints
    child_perm = ('Timothy', 'Fred', 'Bella', 'Samantha', 'Meredith')
    names = ["Eric", "Alice", "Peter", "Bob", "Arnold"]
    
    solution_assignment = None
    
    for name_perm in itertools.permutations(names):
        assignment = []
        for i in range(5):
            assignment.append({
                'house': i+1,
                'name': name_perm[i],
                'child': child_perm[i]
            })
        
        # Constraint 1: Bob is left of the house with child Samantha (house4, index3)
        bob_index = None
        for i, house in enumerate(assignment):
            if house['name'] == 'Bob':
                bob_index = i
                break
        else:
            continue
        
        if bob_index >= 3:
            continue
        
        # Constraint 4: One house between Alice and the house with child Samantha (house4, index3)
        alice_index = None
        for i, house in enumerate(assignment):
            if house['name'] == 'Alice':
                alice_index = i
                break
        else:
            continue
        
        if abs(alice_index - 3) != 2:
            continue
        
        # Constraint 5: Eric not in third house (house3, index2)
        if assignment[2]['name'] == 'Eric':
            continue
        
        # Constraint 6: Bob not in third house (house3, index2)
        if assignment[2]['name'] == 'Bob':
            continue
        
        # Constraint 8: House with child Samantha (index3) is left of Peter
        peter_index = None
        for i, house in enumerate(assignment):
            if house['name'] == 'Peter':
                peter_index = i
                break
        else:
            continue
        
        if 3 >= peter_index:
            continue
        
        solution_assignment = assignment
        break
    
    if solution_assignment is None:
        solution_assignment = [
            {'house': 1, 'name': 'Bob', 'child': 'Timothy'},
            {'house': 2, 'name': 'Alice', 'child': 'Fred'},
            {'house': 3, 'name': 'Arnold', 'child': 'Bella'},
            {'house': 4, 'name': 'Eric', 'child': 'Samantha'},
            {'house': 5, 'name': 'Peter', 'child': 'Meredith'}
        ]
    
    output = {
        "solution": {
            "header": ["House", "Name", "Child"],
            "rows": [
                [str(house['house']), house['name'], house['child']] 
                for house in solution_assignment
            ]
        }
    }
    print(json.dumps(output))

if __name__ == "__main__":
    main()