import itertools
import json

names = ['Eric', 'Arnold', 'Alice', 'Peter']
styles = ['craftsman', 'colonial', 'ranch', 'victorian']

for name_perm in itertools.permutations(names):
    for style_perm in itertools.permutations(styles):
        # Constraint 1: Alice is in the second house
        if name_perm[1] != 'Alice':
            continue
        # Constraint 5: Alice's house is Craftsman
        if style_perm[1] != 'craftsman':
            continue
        # Constraint 2: Victorian directly left of Peter
        victorian_index = style_perm.index('victorian')
        peter_index = name_perm.index('Peter')
        if victorian_index + 1 != peter_index:
            continue
        # Constraint 3: Peter is to the right of ranch
        ranch_index = style_perm.index('ranch')
        if ranch_index >= peter_index:
            continue
        # Constraint 4: Arnold is to the right of Craftsman (house 2, index 1)
        arnold_index = name_perm.index('Arnold')
        if arnold_index <= 1:
            continue
        # Construct the solution
        rows = []
        for i in range(4):
            house_num = str(i + 1)
            name = name_perm[i]
            house_style = style_perm[i]
            rows.append([house_num, name, house_style])
        solution = {
            "solution": {
                "header": ["House", "Name", "HouseStyle"],
                "rows": rows
            }
        }
        print(json.dumps(solution))
        exit()