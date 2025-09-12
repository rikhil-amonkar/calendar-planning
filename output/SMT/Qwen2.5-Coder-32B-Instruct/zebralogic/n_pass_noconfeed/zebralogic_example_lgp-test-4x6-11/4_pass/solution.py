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

    # Map values to integers for each category
    name_map = {name: i for i, name in enumerate(names)}
    hobby_map = {hobby: i for i, hobby in enumerate(hobbies)}
    animal_map = {animal: i for i, animal in enumerate(animals)}
    book_genre_map = {genre: i for i, genre in enumerate(book_genres)}
    birthday_map = {birthday: i for i, birthday in enumerate(birthdays)}
    music_genre_map = {genre: i for i, genre in enumerate(music_genres)}

    # Add constraints based on clues
    solver.add(hobby_vars[hobby_map['cooking']] == book_genre_vars[book_genre_map['romance']])
    solver.add(birthday_vars[birthday_map['feb']] == music_genre_vars[music_genre_map['pop']])
    solver.add(name_vars[name_map['Eric']] != name_vars[name_map['Alice']])
    solver.add(book_genre_vars[book_genre_map['romance']] != book_genre_map['science fiction'])
    solver.add(animal_vars[animal_map['fish']] == birthday_vars[birthday_map['feb']])
    solver.add(name_vars[name_map['Alice']] > book_genre_vars[book_genre_map['fantasy']])
    solver.add(animal_vars[animal_map['horse']] == music_genre_vars[music_genre_map['rock']])
    solver.add(hobby_vars[hobby_map['gardening']] == birthday_vars[birthday_map['april']])
    solver.add(music_genre_vars[music_genre_map['jazz']] == hobby_vars[hobby_map['cooking']])
    solver.add(music_genre_vars[music_genre_map['rock']] == book_genre_vars[book_genre_map['mystery']])
    solver.add(hobby_vars[hobby_map['painting']] == name_vars[name_map['Arnold']] - 1)
    solver.add(name_vars[name_map['Peter']] == music_genre_vars[music_genre_map['pop']])
    solver.add(hobby_vars[hobby_map['gardening']] == name_vars[name_map['Arnold']])
    solver.add(music_genre_vars[music_genre_map['rock']] == birthday_vars[birthday_map['jan']] - 1)
    solver.add(hobby_vars[hobby_map['cooking']] != hobby_vars[hobby_map['photography']])
    solver.add(animal_vars[animal_map['cat']] > animal_vars[animal_map['horse']])

    # Solve the puzzle
    if solver.check() == sat:
        model = solver.model()
        solution = []
        for i in range(4):
            name = names[model.evaluate(name_vars[i]).as_long()]
            hobby = hobbies[model.evaluate(hobby_vars[i]).as_long()]
            animal = animals[model.evaluate(animal_vars[i]).as_long()]
            book_genre = book_genres[model.evaluate(book_genre_vars[i]).as_long()]
            birthday = birthdays[model.evaluate(birthday_vars[i]).as_long()]
            music_genre = music_genres[model.evaluate(music_genre_vars[i]).as_long()]
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