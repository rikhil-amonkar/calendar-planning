import itertools
import json

# Define the possible values for each category
names = ['Eric', 'Arnold', 'Peter']
book_genres = ['mystery', 'science fiction', 'romance']
vacations = ['mountain', 'beach', 'city']

solution_found = None

# Iterate through all permutations of names, book genres, and vacations
for name_perm in itertools.permutations(names):
    for book_perm in itertools.permutations(book_genres):
        for vacation_perm in itertools.permutations(vacations):
            # Check constraint 1: Eric is directly left of Arnold
            eric_pos = name_perm.index('Eric')
            arnold_pos = name_perm.index('Arnold')
            if arnold_pos != eric_pos + 1:
                continue

            # Check constraint 3: Peter prefers city breaks
            peter_pos = name_perm.index('Peter')
            if vacation_perm[peter_pos] != 'city':
                continue

            # Check constraint 5: Science fiction lover loves beach vacations
            sci_fi_index = book_perm.index('science fiction')
            if vacation_perm[sci_fi_index] != 'beach':
                continue

            # Check constraint 4: Mystery lover is to the left of beach lover
            mystery_index = book_perm.index('mystery')
            beach_vacation_index = vacation_perm.index('beach')
            if mystery_index >= beach_vacation_index:
                continue

            # Check constraint 2: Peter is to the right of beach lover
            beach_index = vacation_perm.index('beach')
            if peter_pos <= beach_index:
                continue

            # Construct the solution rows
            rows = []
            for i in range(3):
                house = str(i + 1)
                name = name_perm[i]
                book = book_perm[i]
                vacation = vacation_perm[i]
                rows.append([house, name, book, vacation])

            solution_found = {
                "solution": {
                    "header": ["House", "Name", "BookGenre", "Vacation"],
                    "rows": rows
                }
            }
            # Break out of loops once a solution is found
            break
        if solution_found:
            break
    if solution_found:
        break

# Output the solution as JSON
print(json.dumps(solution_found, indent=2))