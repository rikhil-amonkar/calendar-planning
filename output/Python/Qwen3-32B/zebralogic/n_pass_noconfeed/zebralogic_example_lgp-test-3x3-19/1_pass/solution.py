import itertools
import json

# Generate all permutations and apply constraints

names = ['Eric', 'Arnold', 'Peter']
smoothies = ['desert', 'watermelon', 'cherry']
books = ['science fiction', 'romance', 'mystery']

# Only consider name permutations where the first house is Peter
name_perms = [p for p in itertools.permutations(names) if p[0] == 'Peter']

for name_perm in name_perms:
    for smoothie_perm in itertools.permutations(smoothies):
        for book_perm in itertools.permutations(books):
            # Check clue 2: Arnold loves mystery books
            arnold_index = name_perm.index('Arnold')
            if book_perm[arnold_index] != 'mystery':
                continue
            # Check clue 4: Desert is directly left of mystery (Arnold's house)
            if arnold_index == 0:
                continue  # No house to the left
            if smoothie_perm[arnold_index - 1] != 'desert':
                continue
            # Check clue 1: Cherry is left of mystery (Arnold's position)
            cherry_index = smoothie_perm.index('cherry')
            if cherry_index >= arnold_index:
                continue
            # Check clue 3: Science fiction not in first house
            if book_perm[0] == 'science fiction':
                continue
            # If all constraints are satisfied, build the solution
            solution_rows = []
            for i in range(3):
                house_num = str(i + 1)
                name = name_perm[i]
                smoothie = smoothie_perm[i]
                book = book_perm[i]
                solution_rows.append([house_num, name, smoothie, book])
            solution = {
                "solution": {
                    "header": ["House", "Name", "Smoothie", "BookGenre"],
                    "rows": solution_rows
                }
            }
            print(json.dumps(solution))
            exit()

# If no solution is found (should not happen with a valid puzzle)
print(json.dumps({"solution": {"header": [], "rows": []}}))