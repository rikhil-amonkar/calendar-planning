import itertools
import json

# Define all possible options for each category
names = ['Eric', 'Arnold']
book_genres = ['science fiction', 'mystery']
birthdays = ['april', 'sept']
animals = ['horse', 'cat']

# Generate all permutations for each category
name_perms = list(itertools.permutations(names))
bg_perms = list(itertools.permutations(book_genres))
bd_perms = list(itertools.permutations(birthdays))
animal_perms = list(itertools.permutations(animals))

# Iterate through all possible combinations of permutations
for names_p in name_perms:
    for bg_p in bg_perms:
        for bd_p in bd_perms:
            for animal_p in animal_perms:
                # Clue 1: Eric is in the first house
                if names_p[0] != 'Eric':
                    continue
                # Clue 2: Eric's birthday is September (first house's birthday)
                if bd_p[0] != 'sept':
                    continue
                # Clue 3: science fiction is in the second house
                if bg_p[1] != 'science fiction':
                    continue
                # Clue 4: person with horses has birthday in September
                horse_house = -1
                for i in range(2):
                    if animal_p[i] == 'horse':
                        horse_house = i
                        break
                if bd_p[horse_house] != 'sept':
                    continue
                # If all clues are satisfied, build the solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "BookGenre", "Birthday", "Animal"],
                        "rows": []
                    }
                }
                for i in range(2):
                    house_num = str(i + 1)
                    name = names_p[i]
                    book = bg_p[i]
                    birthday = bd_p[i]
                    animal = animal_p[i]
                    solution['solution']['rows'].append([house_num, name, book, birthday, animal])
                # Output the solution as JSON
                print(json.dumps(solution))
                exit()

# If no solution is found (though there should be one)
print(json.dumps({"solution": {"header": [], "rows": []}}))