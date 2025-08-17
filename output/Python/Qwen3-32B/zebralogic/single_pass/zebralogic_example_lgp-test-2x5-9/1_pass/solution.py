import itertools
import json

# Define all possible permutations for each category
name_perms = list(itertools.permutations(['Arnold', 'Eric']))
book_perms = list(itertools.permutations(['science fiction', 'mystery']))
vacation_perms = list(itertools.permutations(['mountain', 'beach']))
animal_perms = list(itertools.permutations(['cat', 'horse']))
music_perms = list(itertools.permutations(['rock', 'pop']))

# Iterate through all possible combinations of permutations
for combination in itertools.product(name_perms, book_perms, vacation_perms, animal_perms, music_perms):
    names, books, vacations, animals, musics = combination
    
    # Check clue 5: mystery book in first house
    if books[0] != 'mystery':
        continue
    
    # Check clue 4: cat in first house (not in second)
    if animals[0] != 'cat':
        continue
    
    # Check clue 3: rock music in mystery book lover (house 1)
    if musics[0] != 'rock':
        continue
    
    # Check clues 1 and 2: beach vacation is with Eric and pop music
    # Find which house has beach vacation
    beach_house = None
    for i in [0, 1]:
        if vacations[i] == 'beach':
            beach_house = i
            break
    
    # Check if the beach is in house 0 or 1
    # Check if the person is Eric and music is pop
    if names[beach_house] != 'Eric':
        continue
    if musics[beach_house] != 'pop':
        continue
    
    # If all constraints are satisfied, build the solution
    solution = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Vacation", "Animal", "MusicGenre"],
            "rows": [
                ["1", names[0], books[0], vacations[0], animals[0], musics[0]],
                ["2", names[1], books[1], vacations[1], animals[1], musics[1]]
            ]
        }
    }
    
    # Output the JSON and exit
    print(json.dumps(solution))
    break