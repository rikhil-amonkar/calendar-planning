import itertools
import json

names = ['Peter', 'Alice', 'Eric', 'Arnold']
hobbies = ['cooking', 'painting', 'gardening', 'photography']
animals = ['horse', 'fish', 'cat', 'bird']
books = ['fantasy', 'mystery', 'romance', 'science fiction']
birthdays = ['april', 'jan', 'sept', 'feb']
musics = ['pop', 'rock', 'classical', 'jazz']

solution_found = None

for birthday_p in itertools.permutations(birthdays):
    feb_idx = birthday_p.index('feb')
    for names_p in itertools.permutations(names):
        if names_p[feb_idx] != 'Peter':
            continue
        for music_p in itertools.permutations(musics):
            if music_p[feb_idx] != 'pop':
                continue
            for animal_p in itertools.permutations(animals):
                if animal_p[feb_idx] != 'fish':
                    continue
                for hobby_p in itertools.permutations(hobbies):
                    gardening_idx = hobby_p.index('gardening')
                    if names_p[gardening_idx] != 'Arnold':
                        continue
                    if birthday_p[gardening_idx] != 'april':
                        continue
                    for book_p in itertools.permutations(books):
                        cooking_idx = hobby_p.index('cooking')
                        if book_p[cooking_idx] != 'romance':
                            continue
                        jazz_idx = music_p.index('jazz')
                        if hobby_p[jazz_idx] != 'cooking':
                            continue
                        rock_idx = music_p.index('rock')
                        if book_p[rock_idx] != 'mystery':
                            continue
                        horse_idx = animal_p.index('horse')
                        if music_p[horse_idx] != 'rock':
                            continue
                        jan_idx = birthday_p.index('jan')
                        if rock_idx + 1 != jan_idx:
                            continue
                        if cooking_idx == 2:
                            continue
                        painting_idx = hobby_p.index('painting')
                        romance_idx = book_p.index('romance')
                        if painting_idx + 1 != romance_idx:
                            continue
                        eric_idx = names_p.index('Eric')
                        if eric_idx == 1:
                            continue
                        if book_p.index('romance') == 3:
                            continue
                        fantasy_idx = book_p.index('fantasy')
                        alice_idx = names_p.index('Alice')
                        if alice_idx <= fantasy_idx:
                            continue
                        cat_idx = animal_p.index('cat')
                        if cat_idx <= horse_idx:
                            continue
                        houses = []
                        for i in range(4):
                            house = {
                                'House': i + 1,
                                'Name': names_p[i],
                                'Hobby': hobby_p[i],
                                'Animal': animal_p[i],
                                'BookGenre': book_p[i],
                                'Birthday': birthday_p[i],
                                'MusicGenre': music_p[i]
                            }
                            houses.append(house)
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Hobby", "Animal", "BookGenre", "Birthday", "MusicGenre"],
                                "rows": []
                            }
                        }
                        for house in houses:
                            row = [
                                str(house['House']),
                                house['Name'],
                                house['Hobby'],
                                house['Animal'],
                                house['BookGenre'],
                                house['Birthday'],
                                house['MusicGenre']
                            ]
                            solution['solution']['rows'].append(row)
                        print(json.dumps(solution))
                        exit()

print("No solution found")