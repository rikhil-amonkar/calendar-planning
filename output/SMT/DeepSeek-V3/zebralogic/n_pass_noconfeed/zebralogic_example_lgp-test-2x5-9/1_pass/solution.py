import json
from z3 import *

def main():
    # Create solver
    solver = Solver()
    
    # Define attributes
    houses = [1, 2]
    names = ['Arnold', 'Eric']
    book_genres = ['science fiction', 'mystery']
    vacations = ['mountain', 'beach']
    animals = ['cat', 'horse']
    music_genres = ['rock', 'pop']
    
    # Create variables for each attribute per house
    name_vars = {house: String(f'name_{house}') for house in houses}
    book_vars = {house: String(f'book_{house}') for house in houses}
    vacation_vars = {house: String(f'vacation_{house}') for house in houses}
    animal_vars = {house: String(f'animal_{house}') for house in houses}
    music_vars = {house: String(f'music_{house}') for house in houses}
    
    # Each attribute must be one of the allowed values
    for house in houses:
        solver.add(Or([name_vars[house] == name for name in names]))
        solver.add(Or([book_vars[house] == genre for genre in book_genres]))
        solver.add(Or([vacation_vars[house] == vacation for vacation in vacations]))
        solver.add(Or([animal_vars[house] == animal for animal in animals]))
        solver.add(Or([music_vars[house] == genre for genre in music_genres]))
    
    # All attributes must be unique within their category
    for attr_vars in [name_vars, book_vars, vacation_vars, animal_vars, music_vars]:
        solver.add(Distinct([attr_vars[house] for house in houses]))
    
    # Apply clues
    # Clue 1: The person who loves beach vacations is Eric.
    for house in houses:
        solver.add(Implies(vacation_vars[house] == 'beach', name_vars[house] == 'Eric'))
    
    # Clue 2: The person who loves pop music is the person who loves beach vacations.
    for house in houses:
        solver.add(Implies(music_vars[house] == 'pop', vacation_vars[house] == 'beach'))
        solver.add(Implies(vacation_vars[house] == 'beach', music_vars[house] == 'pop'))
    
    # Clue 3: The person who loves rock music is the person who loves mystery books.
    for house in houses:
        solver.add(Implies(music_vars[house] == 'rock', book_vars[house] == 'mystery'))
        solver.add(Implies(book_vars[house] == 'mystery', music_vars[house] == 'rock'))
    
    # Clue 4: The cat lover is not in the second house.
    solver.add(animal_vars[2] != 'cat')
    
    # Clue 5: The person who loves mystery books is in the first house.
    solver.add(book_vars[1] == 'mystery')
    
    # Check if solution exists
    if solver.check() == sat:
        model = solver.model()
        
        # Prepare solution data
        solution = {
            "solution": {
                "header": ["House", "Name", "BookGenre", "Vacation", "Animal", "MusicGenre"],
                "rows": []
            }
        }
        
        for house in sorted(houses):
            name_val = str(model.evaluate(name_vars[house]))
            book_val = str(model.evaluate(book_vars[house]))
            vacation_val = str(model.evaluate(vacation_vars[house]))
            animal_val = str(model.evaluate(animal_vars[house]))
            music_val = str(model.evaluate(music_vars[house]))
            
            solution["solution"]["rows"].append([
                str(house),
                name_val,
                book_val,
                vacation_val,
                animal_val,
                music_val
            ])
        
        # Output as JSON
        print(json.dumps(solution, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()