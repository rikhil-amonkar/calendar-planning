from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
houses = [1, 2, 3, 4]
names = ['Peter', 'Alice', 'Eric', 'Arnold']
hobbies = ['cooking', 'painting', 'gardening', 'photography']
animals = ['horse', 'fish', 'cat', 'bird']
book_genres = ['fantasy', 'mystery', 'romance', 'science fiction']
birthdays = ['april', 'jan', 'sept', 'feb']
music_genres = ['pop', 'rock', 'classical', 'jazz']

# Create dictionaries to hold the variables
name_vars = {house: Int(f'name_{house}') for house in houses}
hobby_vars = {house: Int(f'hobby_{house}') for house in houses}
animal_vars = {house: Int(f'animal_{house}') for house in houses}
book_genre_vars = {house: Int(f'book_genre_{house}') for house in houses}
birthday_vars = {house: Int(f'birthday_{house}') for house in houses}
music_genre_vars = {house: Int(f'music_genre_{house}') for house in houses}

# Add constraints for unique values per category
for var_dict, domain in [(name_vars, names), (hobby_vars, hobbies), (animal_vars, animals),
                         (book_genre_vars, book_genres), (birthday_vars, birthdays), (music_genre_vars, music_genres)]:
    for house in houses:
        solver.add(var_dict[house] >= 0)
        solver.add(var_dict[house] < len(domain))
    for i in range(len(houses)):
        for j in range(i + 1, len(houses)):
            solver.add(var_dict[houses[i]] != var_dict[houses[j]])

# Clue 1: The person who loves cooking is the person who loves romance books.
solver.add(hobby_vars[1] == hobbies.index('cooking') == book_genre_vars[1] == book_genres.index('romance'))

# Clue 2: The person whose birthday is in February is the person who loves pop music.
solver.add(birthday_vars[1] == birthdays.index('feb') == music_genre_vars[1] == music_genres.index('pop'))

# Clue 3: Eric is not in the second house.
solver.add(name_vars[2] != names.index('Eric'))

# Clue 4: The person who loves romance books is not in the fourth house.
solver.add(book_genre_vars[4] != book_genres.index('romance'))

# Clue 5: The person whose birthday is in February is the fish enthusiast.
solver.add(birthday_vars[1] == birthdays.index('feb') == animal_vars[1] == animals.index('fish'))

# Clue 6: Alice is somewhere to the right of the person who loves fantasy books.
solver.add(Or(And(name_vars[2] == names.index('Alice'), book_genre_vars[1] == book_genres.index('fantasy')),
              And(name_vars[3] == names.index('Alice'), Or(book_genre_vars[1] == book_genres.index('fantasy'),
                                                         book_genre_vars[2] == book_genres.index('fantasy'))),
              And(name_vars[4] == names.index('Alice'), Or(book_genre_vars[1] == book_genres.index('fantasy'),
                                                         book_genre_vars[2] == book_genres.index('fantasy'),
                                                         book_genre_vars[3] == book_genres.index('fantasy')))))

# Clue 7: The person who keeps horses is the person who loves rock music.
solver.add(animal_vars[1] == animals.index('horse') == music_genre_vars[1] == music_genres.index('rock'))

# Clue 8: The person who enjoys gardening is the person whose birthday is in April.
solver.add(hobby_vars[1] == hobbies.index('gardening') == birthday_vars[1] == birthdays.index('april'))

# Clue 9: The person who loves jazz music is the person who loves cooking.
solver.add(music_genre_vars[1] == music_genres.index('jazz') == hobby_vars[1] == hobbies.index('cooking'))

# Clue 10: The person who loves rock music is the person who loves mystery books.
solver.add(music_genre_vars[1] == music_genres.index('rock') == book_genre_vars[1] == book_genres.index('mystery'))

# Clue 11: The person who paints as a hobby is directly left of the person who loves romance books.
solver.add(Or(And(hobby_vars[1] == hobbies.index('painting'), book_genre_vars[2] == book_genres.index('romance')),
              And(hobby_vars[2] == hobbies.index('painting'), book_genre_vars[3] == book_genres.index('romance')),
              And(hobby_vars[3] == hobbies.index('painting'), book_genre_vars[4] == book_genres.index('romance'))))

# Clue 12: Peter is the person who loves pop music.
solver.add(name_vars[1] == names.index('Peter') == music_genre_vars[1] == music_genres.index('pop'))

# Clue 13: The person who enjoys gardening is Arnold.
solver.add(hobby_vars[1] == hobbies.index('gardening') == name_vars[1] == names.index('Arnold'))

# Clue 14: The person who loves rock music is directly left of the person whose birthday is in January.
solver.add(Or(And(music_genre_vars[1] == music_genres.index('rock'), birthday_vars[2] == birthdays.index('jan')),
              And(music_genre_vars[2] == music_genres.index('rock'), birthday_vars[3] == birthdays.index('jan')),
              And(music_genre_vars[3] == music_genres.index('rock'), birthday_vars[4] == birthdays.index('jan'))))

# Clue 15: The person who loves cooking is not in the third house.
solver.add(hobby_vars[3] != hobbies.index('cooking'))

# Clue 16: The cat lover is somewhere to the right of the person who keeps horses.
solver.add(Or(And(animal_vars[1] == animals.index('horse'), animal_vars[2] == animals.index('cat')),
              And(animal_vars[1] == animals.index('horse'), animal_vars[3] == animals.index('cat')),
              And(animal_vars[1] == animals.index('horse'), animal_vars[4] == animals.index('cat')),
              And(animal_vars[2] == animals.index('horse'), animal_vars[3] == animals.index('cat')),
              And(animal_vars[2] == animals.index('horse'), animal_vars[4] == animals.index('cat')),
              And(animal_vars[3] == animals.index('horse'), animal_vars[4] == animals.index('cat'))))

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = []
    for house in houses:
        name = names[model[name_vars[house]].as_long()]
        hobby = hobbies[model[hobby_vars[house]].as_long()]
        animal = animals[model[animal_vars[house]].as_long()]
        book_genre = book_genres[model[book_genre_vars[house]].as_long()]
        birthday = birthdays[model[birthday_vars[house]].as_long()]
        music_genre = music_genres[model[music_genre_vars[house]].as_long()]
        solution.append([str(house), name, hobby, animal, book_genre, birthday, music_genre])
    
    # Print the solution in the required JSON format
    print('{' +
          '"solution": {' +
          '"header": ["House", "Name", "Hobby", "Animal", "BookGenre", "Birthday", "MusicGenre"],' +
          f'"rows": {solution}' +
          '}}')
else:
    print("No solution found")