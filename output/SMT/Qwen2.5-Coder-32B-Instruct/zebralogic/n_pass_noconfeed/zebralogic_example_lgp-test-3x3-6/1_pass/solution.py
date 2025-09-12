from z3 import *

def solve_puzzle():
    # Define variables
    names = ['Eric', 'Arnold', 'Peter']
    book_genres = ['mystery', 'science fiction', 'romance']
    vacations = ['mountain', 'beach', 'city']

    # Create integer variables for each attribute in each house
    house_names = [Int(f'house{i}_name') for i in range(1, 4)]
    house_book_genres = [Int(f'house{i}_book_genre') for i in range(1, 4)]
    house_vacations = [Int(f'house{i}_vacation') for i in range(1, 4)]

    # Create solver instance
    solver = Solver()

    # Add constraints for unique values in each category
    solver.add(Distinct(house_names))
    solver.add(Distinct(house_book_genres))
    solver.add(Distinct(house_vacations))

    # Map names, book genres, and vacations to integers
    name_map = {name: i for i, name in enumerate(names)}
    book_genre_map = {genre: i for i, genre in enumerate(book_genres)}
    vacation_map = {vacation: i for i, vacation in enumerate(vacations)}

    # Add constraints based on clues
    # Clue 1: Eric is directly left of Arnold.
    solver.add(house_names[0] == name_map['Eric'])
    solver.add(house_names[1] == name_map['Arnold'])

    # Clue 2: Peter is somewhere to the right of the person who loves beach vacations.
    solver.add(Or(house_vacations[1] == vacation_map['beach'], house_vacations[2] == vacation_map['beach']))
    solver.add(house_names[2] == name_map['Peter'] if house_vacations[1] == vacation_map['beach'] else True)
    solver.add(house_names[2] == name_map['Peter'] if house_vacations[2] == vacation_map['beach'] else True)

    # Clue 3: Peter is the person who prefers city breaks.
    solver.add(house_vacations[2] == vacation_map['city'])

    # Clue 4: The person who loves mystery books is somewhere to the left of the person who loves beach vacations.
    solver.add(Or(
        And(house_book_genres[0] == book_genre_map['mystery'], house_vacations[1] == vacation_map['beach']),
        And(house_book_genres[0] == book_genre_map['mystery'], house_vacations[2] == vacation_map['beach']),
        And(house_book_genres[1] == book_genre_map['mystery'], house_vacations[2] == vacation_map['beach'])
    ))

    # Clue 5: The person who loves science fiction books is the person who loves beach vacations.
    solver.add(house_book_genres[i] == book_genre_map['science fiction'] for i in range(3) if house_vacations[i] == vacation_map['beach'])

    # Check if the problem is solvable
    if solver.check() == sat:
        model = solver.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "BookGenre", "Vacation"],
                "rows": []
            }
        }
        for i in range(3):
            name = names[model.eval(house_names[i]).as_long()]
            book_genre = book_genres[model.eval(house_book_genres[i]).as_long()]
            vacation = vacations[model.eval(house_vacations[i]).as_long()]
            solution["solution"]["rows"].append([str(i + 1), name, book_genre, vacation])
        return solution
    else:
        return None

# Solve the puzzle and print the solution in JSON format
import json
print(json.dumps(solve_puzzle(), indent=2))