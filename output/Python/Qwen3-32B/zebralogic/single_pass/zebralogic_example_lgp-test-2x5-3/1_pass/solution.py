import itertools
import json

# Define the possible options for each category
names = ['Eric', 'Arnold']
hobbies = ['gardening', 'photography']
book_genres = ['science fiction', 'mystery']
music_genres = ['rock', 'pop']
birthdays = ['april', 'sept']

# Generate all permutations for each category
name_perms = list(itertools.permutations(names))
hobby_perms = list(itertools.permutations(hobbies))
book_perms = list(itertools.permutations(book_genres))
music_perms = list(itertools.permutations(music_genres))
birth_perms = list(itertools.permutations(birthdays))

# Iterate through all possible combinations of permutations
for combo in itertools.product(name_perms, hobby_perms, book_perms, music_perms, birth_perms):
    # Unpack the permutations for each category
    names_p, hobbies_p, book_p, music_p, birth_p = combo

    # Check constraint 5: mystery book in first house
    if book_p[0] != 'mystery':
        continue

    # Check constraint 1: mystery book lover loves rock music
    if music_p[0] != 'rock':
        continue

    # Check constraint 3: mystery book lover's hobby is gardening
    if hobbies_p[0] != 'gardening':
        continue

    # Check constraint 2: Arnold is not in first house
    if names_p[0] != 'Eric' or names_p[1] != 'Arnold':
        continue

    # Check constraint 4: Arnold's birthday is April
    april_index = birth_p.index('april')
    if names_p[april_index] != 'Arnold':
        continue

    # If all constraints are met, build the solution
    solution_rows = [
        ["1", names_p[0], hobbies_p[0], book_p[0], music_p[0], birth_p[0]],
        ["2", names_p[1], hobbies_p[1], book_p[1], music_p[1], birth_p[1]]
    ]

    # Construct the JSON output
    solution = {
        "solution": {
            "header": ["House", "Name", "Hobby", "BookGenre", "MusicGenre", "Birthday"],
            "rows": solution_rows
        }
    }

    # Print the JSON solution
    print(json.dumps(solution, indent=2))
    exit()  # Exit after finding the first valid solution