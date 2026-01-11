import itertools
import json

def solve_puzzle():
    # Define the sets of attributes
    names = ['Eric', 'Arnold', 'Peter']
    book_genres = ['mystery', 'science fiction', 'romance']
    vacations = ['mountain', 'beach', 'city']

    # Generate all permutations for the three attributes
    name_permutations = list(itertools.permutations(names))
    book_genre_permutations = list(itertools.permutations(book_genres))
    vacation_permutations = list(itertools.permutations(vacations))

    # Iterate over all combinations of permutations
    for name_perm in name_permutations:
        for book_genre_perm in book_genre_permutations:
            for vacation_perm in vacation_permutations:
                # Create a list of dictionaries representing the houses
                houses = [
                    {"house": 1, "name": name_perm[0], "book_genre": book_genre_perm[0], "vacation": vacation_perm[0]},
                    {"house": 2, "name": name_perm[1], "book_genre": book_genre_perm[1], "vacation": vacation_perm[1]},
                    {"house": 3, "name": name_perm[2], "book_genre": book_genre_perm[2], "vacation": vacation_perm[2]}
                ]

                # Check constraints
                if (houses[0]['name'] == 'Eric' and houses[1]['name'] == 'Arnold' and  # Constraint 1
                    houses.index(next(house for house in houses if house['vacation'] == 'city')) >  # Constraint 2
                    houses.index(next(house for house in houses if house['vacation'] == 'beach')) and
                    houses[houses.index(next(house for house in houses if house['vacation'] == 'city'))]['name'] == 'Peter' and  # Constraint 3
                    houses.index(next(house for house in houses if house['book_genre'] == 'mystery')) <  # Constraint 4
                    houses.index(next(house for house in houses if house['vacation'] == 'beach')) and
                    houses[houses.index(next(house for house in houses if house['vacation'] == 'beach'))]['book_genre'] == 'science fiction'):  # Constraint 5
                    # If all constraints are satisfied, format the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "BookGenre", "Vacation"],
                            "rows": [
                                [str(house['house']), house['name'], house['book_genre'], house['vacation']] for house in houses
                            ]
                        }
                    }
                    return json.dumps(solution, indent=2)

# Solve the puzzle and print the solution
print(solve_puzzle())