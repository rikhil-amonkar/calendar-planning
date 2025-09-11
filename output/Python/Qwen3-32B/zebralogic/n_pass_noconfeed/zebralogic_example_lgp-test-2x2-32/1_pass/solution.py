import itertools
import json

# Define puzzle parameters
names = ['Eric', 'Arnold']
book_genres = ['science fiction', 'mystery']

# Generate all possible permutations for 2 houses
name_permutations = list(itertools.permutations(names))
book_permutations = list(itertools.permutations(book_genres))

solution_data = {"solution": {"header": ["House", "Name", "BookGenre"], "rows": []}}

# Check each combination against constraints
for name_perm in name_permutations:
    for book_perm in book_permutations:
        # Find Eric's position
        eric_pos = None
        for i, name in enumerate(name_perm):
            if name == 'Eric':
                eric_pos = i
                break
                
        # Check if Eric is directly left of mystery reader
        if eric_pos is not None and eric_pos + 1 < 2:
            if book_perm[eric_pos + 1] == 'mystery':
                # Build solution structure
                solution_data["solution"]["rows"] = [
                    ["1", name_perm[0], book_perm[0]],
                    ["2", name_perm[1], book_perm[1]]
                ]
                # Found solution, exit loops
                break
    else:
        # Continue if inner loop wasn't broken
        continue
    # Break outer loop if solution found
    break

# Output JSON
print(json.dumps(solution_data, indent=2))