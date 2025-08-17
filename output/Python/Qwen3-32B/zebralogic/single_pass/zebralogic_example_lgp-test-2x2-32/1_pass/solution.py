import itertools
import json

# Define the possible values
names = ['Eric', 'Arnold']
genres = ['science fiction', 'mystery']

solution_found = None

# Generate all possible permutations for names and genres
for name_perm in itertools.permutations(names):
    for genre_perm in itertools.permutations(genres):
        # Check the clue: Eric is directly left of mystery
        eric_index = name_perm.index('Eric')
        mystery_index = genre_perm.index('mystery')
        # Directly left means eric_index is one less than mystery_index
        if eric_index + 1 == mystery_index:
            # Create the solution rows
            solution_rows = []
            for i in range(2):
                house_num = str(i + 1)
                name = name_perm[i]
                book_genre = genre_perm[i]
                solution_rows.append([house_num, name, book_genre])
            solution_found = {
                "solution": {
                    "header": ["House", "Name", "BookGenre"],
                    "rows": solution_rows
                }
            }
            # Since there's only one solution, break early
            break
    if solution_found:
        break

# Output the solution as JSON
print(json.dumps(solution_found))