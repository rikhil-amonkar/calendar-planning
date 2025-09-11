import itertools
import json

# Define the possible values
names = ['Eric', 'Arnold']
house_styles = ['victorian', 'colonial']

valid_solutions = []

# Generate all possible permutations for styles and names
for style_perm in itertools.permutations(house_styles):
    # Check clue 1: Victorian is left of colonial
    victorian_index = style_perm.index('victorian')
    colonial_index = style_perm.index('colonial')
    if victorian_index < colonial_index:
        # Style permutation is valid. Now check name permutations
        for name_perm in itertools.permutations(names):
            # Check clue 2: Eric is in first house
            if name_perm[0] == 'Eric':
                # Both constraints are satisfied. Build the solution rows.
                rows = []
                for i in range(2):
                    house_num = str(i + 1)
                    name = name_perm[i]
                    style = style_perm[i]
                    rows.append([house_num, name, style])
                valid_solutions.append(rows)

# Since there should be only one valid solution, take the first one
solution = {
    "solution": {
        "header": ["House", "Name", "HouseStyle"],
        "rows": valid_solutions[0]
    }
}

print(json.dumps(solution, indent=2))