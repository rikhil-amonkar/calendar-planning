import itertools
import json

def solve_puzzle():
    # Define the constants
    houses = ['1', '2']
    people = ['Eric', 'Arnold']
    book_genres = ['science fiction', 'mystery']

    # Generate all possible permutations of people and book genres
    all_permutations = list(itertools.permutations(people))
    all_book_permutations = list(itertools.permutations(book_genres))

    # Initialize the solution variable
    solution = None

    # Check each permutation to see if it satisfies the constraint
    for people_order in all_permutations:
        for book_order in all_book_permutations:
            # Create a list of tuples (house, person, book_genre)
            assignments = list(zip(houses, people_order, book_order))
            
            # Check the constraint: Eric is directly left of the person who loves mystery books
            if assignments[0][1] == 'Eric' and assignments[1][2] == 'mystery':
                solution = assignments
                break
        if solution:
            break

    # Format the solution into the required JSON structure
    if solution:
        result = {
            "solution": {
                "header": ["House", "Name", "BookGenre"],
                "rows": [list(row) for row in solution]
            }
        }
        return json.dumps(result, indent=2)
    else:
        return json.dumps({"solution": "No solution found"}, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())