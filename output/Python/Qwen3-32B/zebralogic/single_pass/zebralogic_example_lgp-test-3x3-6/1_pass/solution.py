import itertools
import json

# Define the possible values for each category
names = ['Eric', 'Arnold', 'Peter']
book_genres = ['mystery', 'science fiction', 'romance']
vacations = ['mountain', 'beach', 'city']

# Iterate through all possible permutations
for name_perm in itertools.permutations(names):
    for book_perm in itertools.permutations(book_genres):
        for vacation_perm in itertools.permutations(vacations):
            # Check constraint 1: Eric directly left of Arnold
            eric_pos = name_perm.index('Eric')
            arnold_pos = name_perm.index('Arnold')
            if eric_pos + 1 != arnold_pos:
                continue
            # Check constraint 3: Peter's vacation is city
            peter_pos = name_perm.index('Peter')
            if vacation_perm[peter_pos] != 'city':
                continue
            # Find the beach vacation index
            try:
                beach_vacation_index = vacation_perm.index('beach')
            except ValueError:
                continue
            # Check constraint 2: Peter is to the right of beach
            if peter_pos <= beach_vacation_index:
                continue
            # Check constraint 4: mystery is left of beach
            try:
                mystery_index = book_perm.index('mystery')
            except ValueError:
                continue
            if not (mystery_index < beach_vacation_index):
                continue
            # Check constraint 5: scifi is same as beach
            try:
                scifi_index = book_perm.index('science fiction')
            except ValueError:
                continue
            if scifi_index != beach_vacation_index:
                continue
            # If all constraints are satisfied, build the solution
            rows = []
            for i in range(3):
                house = str(i + 1)
                name = name_perm[i]
                book = book_perm[i]
                vacation = vacation_perm[i]
                rows.append([house, name, book, vacation])
            solution = {
                "solution": {
                    "header": ["House", "Name", "BookGenre", "Vacation"],
                    "rows": rows
                }
            }
            print(json.dumps(solution))
            exit()

# If no solution is found (though there should be one)
print(json.dumps({"solution": {"header": [], "rows": []}}))