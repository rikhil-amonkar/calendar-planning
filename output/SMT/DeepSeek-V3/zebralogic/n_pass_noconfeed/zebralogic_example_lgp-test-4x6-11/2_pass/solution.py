import json
from z3 import *

def main():
    solver = Solver()
    
    n_houses = 4
    houses = [1, 2, 3, 4]
    
    # Define all possible values for each category
    names = ['Peter', 'Alice', 'Eric', 'Arnold']
    hobbies = ['cooking', 'painting', 'gardening', 'photography']
    animals = ['horse', 'fish', 'cat', 'bird']
    book_genres = ['fantasy', 'mystery', 'romance', 'science fiction']
    birthdays = ['april', 'jan', 'sept', 'feb']
    music_genres = ['pop', 'rock', 'classical', 'jazz']
    
    # Create Z3 variables for each attribute in each house
    name_vars = [Int(f'name_{i}') for i in houses]
    hobby_vars = [Int(f'hobby_{i}') for i in houses]
    animal_vars = [Int(f'animal_{i}') for i in houses]
    book_vars = [Int(f'book_{i}') for i in houses]
    birthday_vars = [Int(f'birthday_{i}') for i in houses]
    music_vars = [Int(f'music_{i}') for i in houses]
    
    # Define domains for each variable
    for i in houses:
        solver.add(And(name_vars[i-1] >= 0, name_vars[i-1] < len(names)))
        solver.add(And(hobby_vars[i-1] >= 0, hobby_vars[i-1] < len(hobbies)))
        solver.add(And(animal_vars[i-1] >= 0, animal_vars[i-1] < len(animals)))
        solver.add(And(book_vars[i-1] >= 0, book_vars[i-1] < len(book_genres)))
        solver.add(And(birthday_vars[i-1] >= 0, birthday_vars[i-1] < len(birthdays)))
        solver.add(And(music_vars[i-1] >= 0, music_vars[i-1] < len(music_genres)))
    
    # All attributes are distinct within their category
    solver.add(Distinct(name_vars))
    solver.add(Distinct(hobby_vars))
    solver.add(Distinct(animal_vars))
    solver.add(Distinct(book_vars))
    solver.add(Distinct(birthday_vars))
    solver.add(Distinct(music_vars))
    
    # Clue 1: The person who loves cooking is the person who loves romance books.
    for i in houses:
        solver.add(Implies(hobby_vars[i-1] == hobbies.index('cooking'), 
                          book_vars[i-1] == book_genres.index('romance')))
    
    # Clue 2: The person whose birthday is in February is the person who loves pop music.
    for i in houses:
        solver.add(Implies(birthday_vars[i-1] == birthdays.index('feb'), 
                          music_vars[i-1] == music_genres.index('pop')))
    
    # Clue 3: Eric is not in the second house.
    solver.add(name_vars[1] != names.index('Eric'))
    
    # Clue 4: The person who loves romance books is not in the fourth house.
    solver.add(book_vars[3] != book_genres.index('romance'))
    
    # Clue 5: The person whose birthday is in February is the fish enthusiast.
    for i in houses:
        solver.add(Implies(birthday_vars[i-1] == birthdays.index('feb'), 
                          animal_vars[i-1] == animals.index('fish')))
    
    # Clue 6: Alice is somewhere to the right of the person who loves fantasy books.
    # Create constraints for Alice being right of fantasy book lover
    alice_right_of_fantasy = []
    for i in houses:
        for j in houses:
            if i > j:  # house i is right of house j
                alice_right_of_fantasy.append(And(
                    name_vars[i-1] == names.index('Alice'),
                    book_vars[j-1] == book_genres.index('fantasy')
                ))
    solver.add(Or(alice_right_of_fantasy))
    
    # Clue 7: The person who keeps horses is the person who loves rock music.
    for i in houses:
        solver.add(Implies(animal_vars[i-1] == animals.index('horse'), 
                          music_vars[i-1] == music_genres.index('rock')))
    
    # Clue 8: The person who enjoys gardening is the person whose birthday is in April.
    for i in houses:
        solver.add(Implies(hobby_vars[i-1] == hobbies.index('gardening'), 
                          birthday_vars[i-1] == birthdays.index('april')))
    
    # Clue 9: The person who loves jazz music is the person who loves cooking.
    for i in houses:
        solver.add(Implies(music_vars[i-1] == music_genres.index('jazz'), 
                          hobby_vars[i-1] == hobbies.index('cooking')))
    
    # Clue 10: The person who loves rock music is the person who loves mystery books.
    for i in houses:
        solver.add(Implies(music_vars[i-1] == music_genres.index('rock'), 
                          book_vars[i-1] == book_genres.index('mystery')))
    
    # Clue 11: The person who paints as a hobby is directly left of the person who loves romance books.
    painting_left_of_romance = []
    for i in range(1, n_houses):  # i from 1 to 3 (0-indexed)
        painting_left_of_romance.append(And(
            hobby_vars[i-1] == hobbies.index('painting'),
            book_vars[i] == book_genres.index('romance')
        ))
    solver.add(Or(painting_left_of_romance))
    
    # Clue 12: Peter is the person who loves pop music.
    for i in houses:
        solver.add(Implies(name_vars[i-1] == names.index('Peter'), 
                          music_vars[i-1] == music_genres.index('pop')))
    
    # Clue 13: The person who enjoys gardening is Arnold.
    for i in houses:
        solver.add(Implies(hobby_vars[i-1] == hobbies.index('gardening'), 
                          name_vars[i-1] == names.index('Arnold')))
    
    # Clue 14: The person who loves rock music is directly left of the person whose birthday is in January.
    rock_left_of_jan = []
    for i in range(1, n_houses):  # i from 1 to 3 (0-indexed)
        rock_left_of_jan.append(And(
            music_vars[i-1] == music_genres.index('rock'),
            birthday_vars[i] == birthdays.index('jan')
        ))
    solver.add(Or(rock_left_of_jan))
    
    # Clue 15: The person who loves cooking is not in the third house.
    solver.add(hobby_vars[2] != hobbies.index('cooking'))
    
    # Clue 16: The cat lover is somewhere to the right of the person who keeps horses.
    cat_right_of_horse = []
    for i in houses:
        for j in houses:
            if i > j:  # house i is right of house j
                cat_right_of_horse.append(And(
                    animal_vars[i-1] == animals.index('cat'),
                    animal_vars[j-1] == animals.index('horse')
                ))
    solver.add(Or(cat_right_of_horse))
    
    # Check if the problem is satisfiable
    if solver.check() == sat:
        model = solver.model()
        
        # Extract the solution
        solution = []
        for house in houses:
            idx = house - 1
            name_idx = model.evaluate(name_vars[idx]).as_long()
            hobby_idx = model.evaluate(hobby_vars[idx]).as_long()
            animal_idx = model.evaluate(animal_vars[idx]).as_long()
            book_idx = model.evaluate(book_vars[idx]).as_long()
            birthday_idx = model.evaluate(birthday_vars[idx]).as_long()
            music_idx = model.evaluate(music_vars[idx]).as_long()
            
            row = [
                str(house),
                names[name_idx],
                hobbies[hobby_idx],
                animals[animal_idx],
                book_genres[book_idx],
                birthdays[birthday_idx],
                music_genres[music_idx]
            ]
            solution.append(row)
        
        # Format the output as JSON
        output = {
            "solution": {
                "header": ["House", "Name", "Hobby", "Animal", "BookGenre", "Birthday", "MusicGenre"],
                "rows": solution
            }
        }
        
        print(json.dumps(output, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()