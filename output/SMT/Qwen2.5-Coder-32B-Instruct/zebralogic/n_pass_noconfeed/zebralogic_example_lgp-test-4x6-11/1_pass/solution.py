from z3 import *

def solve_puzzle():
    # Define the variables
    names = ['Peter', 'Alice', 'Eric', 'Arnold']
    hobbies = ['cooking', 'painting', 'gardening', 'photography']
    animals = ['horse', 'fish', 'cat', 'bird']
    book_genres = ['fantasy', 'mystery', 'romance', 'science fiction']
    birthdays = ['april', 'jan', 'sept', 'feb']
    music_genres = ['pop', 'rock', 'classical', 'jazz']

    # Create a solver instance
    solver = Solver()

    # Create arrays for each attribute
    name_vars = [Int(f'name_{i}') for i in range(4)]
    hobby_vars = [Int(f'hobby_{i}') for i in range(4)]
    animal_vars = [Int(f'animal_{i}') for i in range(4)]
    book_genre_vars = [Int(f'book_genre_{i}') for i in range(4)]
    birthday_vars = [Int(f'birthday_{i}') for i in range(4)]
    music_genre_vars = [Int(f'music_genre_{i}') for i in range(4)]

    # Add constraints for unique values in each category
    for vars in [name_vars, hobby_vars, animal_vars, book_genre_vars, birthday_vars, music_genre_vars]:
        solver.add(Distinct(vars))

    # Map values to integers
    value_map = {v: i for i, v in enumerate(names + hobbies + animals + book_genres + birthdays + music_genres)}

    # Add constraints based on clues
    solver.add(hobby_vars[value_map['cooking']] == book_genre_vars[value_map['romance']])
    solver.add(birthday_vars[value_map['feb']] == music_genre_vars[value_map['pop']])
    solver.add(name_vars[value_map['Eric']] != 1)
    solver.add(book_genre_vars[value_map['romance']] != 3)
    solver.add(animal_vars[value_map['fish']] == birthday_vars[value_map['feb']])
    solver.add(name_vars.index(value_map['Alice']) > name_vars.index(value_map['fantasy']))
    solver.add(animal_vars[value_map['horse']] == music_genre_vars[value_map['rock']])
    solver.add(hobby_vars[value_map['gardening']] == birthday_vars[value_map['april']])
    solver.add(music_genre_vars[value_map['jazz']] == hobby_vars[value_map['cooking']])
    solver.add(music_genre_vars[value_map['rock']] == book_genre_vars[value_map['mystery']])
    solver.add(hobby_vars[value_map['painting']] == name_vars.index(value_map['romance']) - 1)
    solver.add(name_vars[value_map['Peter']] == music_genre_vars[value_map['pop']])
    solver.add(hobby_vars[value_map['gardening']] == name_vars[value_map['Arnold']])
    solver.add(music_genre_vars[value_map['rock']] == birthday_vars[value_map['jan']] - 1)
    solver.add(hobby_vars[value_map['cooking']] != 2)
    solver.add(animal_vars[value_map['cat']] > animal_vars[value_map['horse']])

    # Solve the puzzle
    if solver.check() == sat:
        model = solver.model()
        solution = []
        for i in range(4):
            name = names[model.evaluate(name_vars[i]).as_long()]
            hobby = hobbies[model.evaluate(hobby_vars[i]).as_long() - 4]
            animal = animals[model.evaluate(animal_vars[i]).as_long() - 8]
            book_genre = book_genres[model.evaluate(book_genre_vars[i]).as_long() - 12]
            birthday = birthdays[model.evaluate(birthday_vars[i]).as_long() - 16]
            music_genre = music_genres[model.evaluate(music_genre_vars[i]).as_long() - 20]
            solution.append([str(i + 1), name, hobby, animal, book_genre, birthday, music_genre])
        return {
            "solution": {
                "header": ["House", "Name", "Hobby", "Animal", "BookGenre", "Birthday", "MusicGenre"],
                "rows": solution
            }
        }
    else:
        return None

# Output the solution as JSON
import json
print(json.dumps(solve_puzzle(), indent=2))