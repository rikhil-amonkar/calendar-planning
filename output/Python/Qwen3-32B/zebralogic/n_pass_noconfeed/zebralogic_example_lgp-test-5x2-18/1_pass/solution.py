import itertools
import json

# Define the names and children
names = ['Eric', 'Alice', 'Peter', 'Bob', 'Arnold']
children = ['Timothy', 'Meredith', 'Samantha', 'Fred', 'Bella']

# Generate valid name permutations (Eric and Bob not in the third house)
valid_name_perms = [p for p in itertools.permutations(names) if p[2] not in ['Eric', 'Bob']]

# Generate valid children permutations (Fred in house 2, Bella directly to the right of Fred)
children_options = []
remaining_children = ['Timothy', 'Meredith', 'Samantha']
for p in itertools.permutations(remaining_children):
    children_perm = [p[0], 'Fred', 'Bella', p[1], p[2]]
    children_options.append(children_perm)

# Search for the solution
found = False
for name_perm in valid_name_perms:
    for children_perm in children_options:
        # Find positions for Samantha and Timothy
        samantha_pos = children_perm.index('Samantha')
        timothy_pos = children_perm.index('Timothy')
        
        # Check Clue 2: Mother of Timothy is to the left of Samantha
        if timothy_pos >= samantha_pos:
            continue
        
        # Check Clue 1: Bob is to the left of Samantha
        bob_pos = name_perm.index('Bob')
        if bob_pos >= samantha_pos:
            continue
        
        # Check Clue 4: One house between Alice and Samantha
        alice_pos = name_perm.index('Alice')
        if abs(alice_pos - samantha_pos) != 2:
            continue
        
        # Check Clue 8: Samantha is to the left of Peter
        peter_pos = name_perm.index('Peter')
        if samantha_pos >= peter_pos:
            continue
        
        # Build the solution
        solution_data = {
            "solution": {
                "header": ["House", "Name", "Children"],
                "rows": []
            }
        }
        for i in range(5):
            house_num = str(i + 1)
            name = name_perm[i]
            child = children_perm[i]
            solution_data['solution']['rows'].append([house_num, name, child])
        
        # Output the JSON
        print(json.dumps(solution_data))
        found = True
        break
    if found:
        break