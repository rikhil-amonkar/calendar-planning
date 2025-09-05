import z3
import json

def main():
    solver = z3.Solver()
    
    # Define the attributes and their possible values
    names = ['Arnold', 'Eric']
    book_genres = ['science fiction', 'mystery']
    vacations = ['mountain', 'beach']
    animals = ['cat', 'horse']
    music_genres = ['rock', 'pop']
    
    # Create enums for each attribute type and get both the sort and constants
    NameSort, name_consts = z3.EnumSort('Name', names)
    BookGenreSort, book_genre_consts = z3.EnumSort('BookGenre', book_genres)
    VacationSort, vacation_consts = z3.EnumSort('Vacation', vacations)
    AnimalSort, animal_consts = z3.EnumSort('Animal', animals)
    MusicGenreSort, music_genre_consts = z3.EnumSort('MusicGenre', music_genres)
    
    # Create variables for each house and each attribute using the correct sorts
    houses = [1, 2]
    attrs = {
        'name': [z3.Const(f'name_{i}', NameSort) for i in houses],
        'book_genre': [z3.Const(f'book_genre_{i}', BookGenreSort) for i in houses],
        'vacation': [z3.Const(f'vacation_{i}', VacationSort) for i in houses],
        'animal': [z3.Const(f'animal_{i}', AnimalSort) for i in houses],
        'music_genre': [z3.Const(f'music_genre_{i}', MusicGenreSort) for i in houses]
    }
    
    # Each attribute must be one of the defined values (implicit in EnumSort)
    # All attributes within a category must be distinct
    for attr in attrs.values():
        solver.add(z3.Distinct(attr))
    
    # Get constants for specific values
    beach = vacation_consts[vacations.index('beach')]
    eric = name_consts[names.index('Eric')]
    pop = music_genre_consts[music_genres.index('pop')]
    rock = music_genre_consts[music_genres.index('rock')]
    mystery = book_genre_consts[book_genres.index('mystery')]
    cat = animal_consts[animals.index('cat')]
    
    # Clue 1: The person who loves beach vacations is Eric.
    for i in houses:
        solver.add(z3.Implies(attrs['vacation'][i-1] == beach, attrs['name'][i-1] == eric))
    
    # Clue 2: The person who loves pop music is the person who loves beach vacations.
    for i in houses:
        solver.add(z3.Implies(attrs['music_genre'][i-1] == pop, attrs['vacation'][i-1] == beach))
    
    # Clue 3: The person who loves rock music is the person who loves mystery books.
    for i in houses:
        solver.add(z3.Implies(attrs['music_genre'][i-1] == rock, attrs['book_genre'][i-1] == mystery))
    
    # Clue 4: The cat lover is not in the second house.
    solver.add(attrs['animal'][1] != cat)
    
    # Clue 5: The person who loves mystery books is in the first house.
    solver.add(attrs['book_genre'][0] == mystery)
    
    # Check if the problem is satisfiable
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Map house numbers to their attribute values
        result = []
        for i in range(2):
            house_num = str(i+1)
            name_val = str(model.eval(attrs['name'][i]))
            book_val = str(model.eval(attrs['book_genre'][i]))
            vacation_val = str(model.eval(attrs['vacation'][i]))
            animal_val = str(model.eval(attrs['animal'][i]))
            music_val = str(model.eval(attrs['music_genre'][i]))
            
            result.append([house_num, name_val, book_val, vacation_val, animal_val, music_val])
        
        # Format the output as JSON
        output = {
            "solution": {
                "header": ["House", "Name", "BookGenre", "Vacation", "Animal", "MusicGenre"],
                "rows": result
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == '__main__':
    main()