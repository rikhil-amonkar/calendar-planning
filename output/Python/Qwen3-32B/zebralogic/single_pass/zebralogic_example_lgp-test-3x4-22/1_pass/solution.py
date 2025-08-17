import itertools
import json

names = ['Arnold', 'Eric', 'Peter']
music_genres = ['pop', 'rock', 'classical']
children = ['Fred', 'Meredith', 'Bella']
book_genres = ['mystery', 'romance', 'science fiction']

for name_perm in itertools.permutations(names):
    if name_perm[0] != 'Peter':
        continue
    for music_perm in itertools.permutations(music_genres):
        for children_perm in itertools.permutations(children):
            for book_perm in itertools.permutations(book_genres):
                # Check clue 5: Eric's book is mystery
                eric_index = None
                for i in range(3):
                    if name_perm[i] == 'Eric':
                        eric_index = i
                        break
                if book_perm[eric_index] != 'mystery':
                    continue
                # Check clue 3: Eric's music is classical
                if music_perm[eric_index] != 'classical':
                    continue
                # Check clue 1: child Fred is directly left of mystery book
                fred_index = None
                for i in range(3):
                    if children_perm[i] == 'Fred':
                        fred_index = i
                        break
                if fred_index + 1 >= 3 or book_perm[fred_index + 1] != 'mystery':
                    continue
                # Check clue 4: science fiction book has child Meredith
                sci_fi_index = None
                for i in range(3):
                    if book_perm[i] == 'science fiction':
                        sci_fi_index = i
                        break
                if children_perm[sci_fi_index] != 'Meredith':
                    continue
                # Check clue 6: rock music is to the right of romance book
                romance_book_index = None
                for i in range(3):
                    if book_perm[i] == 'romance':
                        romance_book_index = i
                rock_music_index = None
                for i in range(3):
                    if music_perm[i] == 'rock':
                        rock_music_index = i
                if romance_book_index is None or rock_music_index is None:
                    continue
                if not (rock_music_index > romance_book_index):
                    continue
                # If all constraints are satisfied, build the solution
                solution_rows = []
                for i in range(3):
                    house = str(i + 1)
                    solution_rows.append([
                        house,
                        name_perm[i],
                        music_perm[i],
                        children_perm[i],
                        book_perm[i]
                    ])
                solution_dict = {
                    "solution": {
                        "header": ["House", "Name", "MusicGenre", "Children", "BookGenre"],
                        "rows": solution_rows
                    }
                }
                print(json.dumps(solution_dict, indent=2))
                exit()