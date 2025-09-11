import itertools
import json

# Generate all possible permutations for the first two names (Alice and Peter)
possible_name_heads = itertools.permutations(['Alice', 'Peter'])

for name_head in possible_name_heads:
    names = list(name_head) + ['Eric', 'Arnold']
    # Find Alice's house (1-based index)
    alice_house = None
    for i in range(4):
        if names[i] == 'Alice':
            alice_house = i + 1
            break
    # Generate all possible permutations for the styles (excluding Craftsman for house 3)
    for style_perm in itertools.permutations(['victorian', 'ranch', 'colonial']):
        styles = [None] * 4
        styles[0] = style_perm[0]  # House 1
        styles[1] = style_perm[1]  # House 2
        styles[3] = style_perm[2]  # House 4
        styles[2] = 'craftsman'    # House 3 (fixed)
        # Check if Alice's house has 'victorian' style
        alice_index = alice_house - 1
        if styles[alice_index] != 'victorian':
            continue
        # Check if there's a ranch directly to the left of the Victorian house
        if alice_index > 0 and styles[alice_index - 1] == 'ranch':
            # Construct the solution
            rows = []
            for house_num in range(1, 5):
                name = names[house_num - 1]
                style = styles[house_num - 1]
                rows.append([str(house_num), name, style])
            solution = {
                "solution": {
                    "header": ["House", "Name", "HouseStyle"],
                    "rows": rows
                }
            }
            print(json.dumps(solution))
            exit()

# Fallback in case no solution is found (should not occur with valid puzzle)
print(json.dumps({"solution": {"header": ["House", "Name", "HouseStyle"], "rows": []}}))