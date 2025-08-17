import itertools
import json

# Generate all possible permutations for each category
names_list = list(itertools.permutations(['Eric', 'Arnold'], 2))
children_list = list(itertools.permutations(['Bella', 'Fred'], 2))
foods_list = list(itertools.permutations(['grilled cheese', 'pizza'], 2))

solution_found = None

for names in names_list:
    for children in children_list:
        for foods in foods_list:
            # Check clue 1: Arnold has pizza
            valid = True
            for i in range(2):
                if names[i] == 'Arnold' and foods[i] != 'pizza':
                    valid = False
                    break
            if not valid:
                continue
            
            # Check clue 2: grilled cheese is directly left of the person whose child is Fred
            pos_grilled = foods.index('grilled cheese')
            if pos_grilled == 0 and children[1] == 'Fred':
                # Construct the solution
                rows = []
                for i in range(2):
                    house = i + 1
                    name = names[i]
                    child = children[i]
                    food = foods[i]
                    rows.append([str(house), name, child, food])
                solution_found = {
                    "solution": {
                        "header": ["House", "Name", "Children", "Food"],
                        "rows": rows
                    }
                }
                break  # Exit inner loops
            else:
                continue
            break
        if solution_found:
            break
    if solution_found:
        break

# Output the solution as JSON
print(json.dumps(solution_found))