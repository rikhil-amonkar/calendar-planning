import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Bob', 'Arnold', 'Carol', 'Alice', 'Peter', 'Eric']
    book_genres = ['romance', 'historical fiction', 'biography', 'mystery', 'fantasy', 'science fiction']
    occupations = ['artist', 'doctor', 'nurse', 'engineer', 'teacher', 'lawyer']

    # Generate all possible permutations
    for name_perm in itertools.permutations(names):
        for genre_perm in itertools.permutations(book_genres):
            for occ_perm in itertools.permutations(occupations):
                # Create a dictionary to store the current permutation
                current_solution = {house: {'Name': name, 'BookGenre': genre, 'Occupation': occ}
                                    for house, name, genre, occ in zip(houses, name_perm, genre_perm, occ_perm)}

                # Check all constraints
                if (current_solution[1]['Name'] == 'Alice' and current_solution[1]['BookGenre'] == 'fantasy' and
                    abs(name_perm.index('Bob') - genre_perm.index('mystery')) == 1 and
                    current_solution[name_perm.index('Carol') + 1]['BookGenre'] == 'mystery' and
                    current_solution[genre_perm.index('fantasy') + 1]['Occupation'] == 'lawyer' and
                    name_perm.index('Bob') != 4 and
                    name_perm.index('Arnold') < occ_perm.index('engineer') and
                    current_solution[name_perm.index('Alice')]['Occupation'] == 'nurse' and
                    current_solution[genre_perm.index('biography') + 1]['Occupation'] == 'teacher' and
                    genre_perm.index('historical fiction') < occ_perm.index('teacher') and
                    current_solution[1]['Occupation'] == 'doctor' and
                    current_solution[genre_perm.index('science fiction') + 1]['Occupation'] == 'artist' and
                    name_perm[2] == 'Eric' and
                    genre_perm.index('mystery') != 4):
                    
                    # Format the solution as required
                    solution_rows = [[str(house), current_solution[house]['Name'], current_solution[house]['BookGenre'], current_solution[house]['Occupation']]
                                     for house in houses]
                    solution_dict = {
                        "solution": {
                            "header": ["House", "Name", "BookGenre", "Occupation"],
                            "rows": solution_rows
                        }
                    }
                    return json.dumps(solution_dict, indent=2)

# Output the solution
print(solve_puzzle())