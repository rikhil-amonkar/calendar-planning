import itertools
import json

# Define the possible values for each category
names = ["Arnold", "Eric"]
book_genres = ["science fiction", "mystery"]
vacations = ["mountain", "beach"]
animals = ["cat", "horse"]
music_genres = ["rock", "pop"]

# Generate all permutations for each category
name_perms = itertools.permutations(names)
book_perms = itertools.permutations(book_genres)
vacation_perms = itertools.permutations(vacations)
animal_perms = itertools.permutations(animals)
music_perms = itertools.permutations(music_genres)

# Iterate through all possible combinations of permutations
for combo in itertools.product(name_perms, book_perms, vacation_perms, animal_perms, music_perms):
    # Extract each permutation for easier reading
    names_p = combo[0]
    books_p = combo[1]
    vacations_p = combo[2]
    animals_p = combo[3]
    music_p = combo[4]

    # Check clue 5: The mystery book lover is in the first house
    if books_p[0] != 'mystery':
        continue

    # Check clue 4: The cat lover is not in the second house
    if animals_p[0] != 'cat':
        continue

    # Check clue 3: Rock music lover is the mystery book lover (house 1)
    if music_p[0] != 'rock':
        continue

    # Find the house with beach vacation
    beach_house = None
    for i in [0, 1]:
        if vacations_p[i] == 'beach':
            beach_house = i
            break

    # Check clue 1 and 2: Eric is the beach vacation lover and loves pop music
    if beach_house is not None:
        if names_p[beach_house] != 'Eric':
            continue
        if music_p[beach_house] != 'pop':
            continue
    else:
        continue  # No beach vacation found (should not happen)

    # If all constraints are satisfied, build the solution
    solution_data = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Vacation", "Animal", "MusicGenre"],
            "rows": []
        }
    }

    # Populate the rows
    for i in [0, 1]:
        house_num = str(i + 1)
        name = names_p[i]
        book = books_p[i]
        vacation = vacations_p[i]
        animal = animals_p[i]
        music = music_p[i]
        solution_data['solution']['rows'].append([
            house_num, name, book, vacation, animal, music
        ])

    # Output the JSON
    print(json.dumps(solution_data, indent=2))
    exit()

# If no solution found (shouldn't happen)
print(json.dumps({"solution": {"header": [], "rows": []}}))