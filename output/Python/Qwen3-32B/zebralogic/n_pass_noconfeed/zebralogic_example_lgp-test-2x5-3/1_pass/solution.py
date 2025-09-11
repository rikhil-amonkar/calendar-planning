import itertools
import json

# Define the possible values for each category
names = ['Eric', 'Arnold']
hobbies = ['gardening', 'photography']
book_genres = ['science fiction', 'mystery']
music_genres = ['rock', 'pop']
birthdays = ['april', 'sept']

# Generate all possible permutations for each category
name_perms = list(itertools.permutations(names))
hobby_perms = list(itertools.permutations(hobbies))
book_perms = list(itertools.permutations(book_genres))
music_perms = list(itertools.permutations(music_genres))
birthday_perms = list(itertools.permutations(birthdays))

solution_found = None

for name_p in name_perms:
    for hobby_p in hobby_perms:
        for book_p in book_perms:
            # Check constraint 5: mystery in first house
            if book_p[0] != 'mystery':
                continue
            for music_p in music_perms:
                # Check constraint 1: mystery (house 1) has rock music
                if music_p[0] != 'rock':
                    continue
                for birthday_p in birthday_perms:
                    # Check constraint 2: Arnold not in first house
                    if name_p[0] != 'Eric':
                        continue
                    # Check constraint 3: hobby of house 1 is gardening
                    if hobby_p[0] != 'gardening':
                        continue
                    # Check constraint 4: person with april is Arnold
                    april_house = -1
                    for i in range(2):
                        if birthday_p[i] == 'april':
                            april_house = i
                            break
                    if april_house == -1 or name_p[april_house] != 'Arnold':
                        continue
                    # All constraints are satisfied. Build the solution.
                    rows = [
                        ["1", name_p[0], hobby_p[0], book_p[0], music_p[0], birthday_p[0]],
                        ["2", name_p[1], hobby_p[1], book_p[1], music_p[1], birthday_p[1]]
                    ]
                    solution_found = {
                        "solution": {
                            "header": ["House", "Name", "Hobby", "BookGenre", "MusicGenre", "Birthday"],
                            "rows": rows
                        }
                    }
                    break
                if solution_found:
                    break
            if solution_found:
                break
        if solution_found:
            break
    if solution_found:
        break

# Output the solution as JSON
print(json.dumps(solution_found, indent=2))