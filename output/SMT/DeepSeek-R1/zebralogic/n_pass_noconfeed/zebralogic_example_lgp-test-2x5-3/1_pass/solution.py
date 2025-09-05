import json
from z3 import *

def main():
    # Initialize the solver
    solver = Solver()
    
    # Define the attributes and their possible values
    names = ['Eric', 'Arnold']
    hobbies = ['gardening', 'photography']
    book_genres = ['science fiction', 'mystery']
    music_genres = ['rock', 'pop']
    birthdays = ['april', 'sept']
    
    # Create Z3 variables for each attribute for each house
    name_vars = [Int(f'name_{i}') for i in range(2)]
    hobby_vars = [Int(f'hobby_{i}') for i in range(2)]
    book_vars = [Int(f'book_{i}') for i in range(2)]
    music_vars = [Int(f'music_{i}') for i in range(2)]
    birthday_vars = [Int(f'birthday_{i}') for i in range(2)]
    
    # Constrain each variable to its domain
    for i in range(2):
        solver.add(name_vars[i] >= 0, name_vars[i] < len(names))
        solver.add(hobby_vars[i] >= 0, hobby_vars[i] < len(hobbies))
        solver.add(book_vars[i] >= 0, book_vars[i] < len(book_genres))
        solver.add(music_vars[i] >= 0, music_vars[i] < len(music_genres))
        solver.add(birthday_vars[i] >= 0, birthday_vars[i] < len(birthdays))
    
    # Ensure all attributes are distinct per category
    solver.add(Distinct(name_vars))
    solver.add(Distinct(hobby_vars))
    solver.add(Distinct(book_vars))
    solver.add(Distinct(music_vars))
    solver.add(Distinct(birthday_vars))
    
    # Add clue constraints
    # Clue 1: The person who loves mystery books is the person who loves rock music.
    for i in range(2):
        solver.add(Implies(book_vars[i] == book_genres.index('mystery'), music_vars[i] == music_genres.index('rock')))
        solver.add(Implies(music_vars[i] == music_genres.index('rock'), book_vars[i] == book_genres.index('mystery')))
    
    # Clue 2: Arnold is not in the first house.
    solver.add(name_vars[0] != names.index('Arnold'))
    
    # Clue 3: The person who loves mystery books is the person who enjoys gardening.
    for i in range(2):
        solver.add(Implies(book_vars[i] == book_genres.index('mystery'), hobby_vars[i] == hobbies.index('gardening')))
        solver.add(Implies(hobby_vars[i] == hobbies.index('gardening'), book_vars[i] == book_genres.index('mystery')))
    
    # Clue 4: The person whose birthday is in April is Arnold.
    for i in range(2):
        solver.add(Implies(birthday_vars[i] == birthdays.index('april'), name_vars[i] == names.index('Arnold')))
        solver.add(Implies(name_vars[i] == names.index('Arnold'), birthday_vars[i] == birthdays.index('april')))
    
    # Clue 5: The person who loves mystery books is in the first house.
    solver.add(book_vars[0] == book_genres.index('mystery'))
    
    # Check if the problem is satisfiable
    if solver.check() == sat:
        model = solver.model()
        
        # Map house indices to attribute values
        solution_rows = []
        for i in range(2):
            name_val = names[model.evaluate(name_vars[i]).as_long()]
            hobby_val = hobbies[model.evaluate(hobby_vars[i]).as_long()]
            book_val = book_genres[model.evaluate(book_vars[i]).as_long()]
            music_val = music_genres[model.evaluate(music_vars[i]).as_long()]
            birthday_val = birthdays[model.evaluate(birthday_vars[i]).as_long()]
            
            solution_rows.append([str(i+1), name_val, hobby_val, book_val, music_val, birthday_val])
        
        # Create the solution dictionary
        solution_dict = {
            "solution": {
                "header": ["House", "Name", "Hobby", "BookGenre", "MusicGenre", "Birthday"],
                "rows": solution_rows
            }
        }
        
        # Output the JSON
        print(json.dumps(solution_dict, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()