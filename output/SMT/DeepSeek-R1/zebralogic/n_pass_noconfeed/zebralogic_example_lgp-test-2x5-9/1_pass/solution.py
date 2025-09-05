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
    
    # Create enums for each attribute type
    Name = z3.EnumSort('Name', names)
    BookGenre = z3.EnumSort('BookGenre', book_genres)
    Vacation = z3.EnumSort('Vacation', vacations)
    Animal = z3.EnumSort('Animal', animals)
    MusicGenre = z3.EnumSort('MusicGenre', music_genres)
    
    # Create variables for each house and each attribute
    houses = [1, 2]
    attrs = {
        'name': [z3.Const(f'name_{i}', Name) for i in houses],
        'book_genre': [z3.Const(f'book_genre_{i}', BookGenre) for i in houses],
        'vacation': [z3.Const(f'vacation_{i}', Vacation) for i in houses],
        'animal': [z3.Const(f'animal_{i}', Animal) for i in houses],
        'music_genre': [z3.Const(f'music_genre_{i}', MusicGenre) for i in houses]
    }
    
    # Each attribute must be one of the defined values (implicit in EnumSort)
    # All attributes within a category must be distinct
    for attr in attrs.values():
        solver.add(z3.Distinct(attr))
    
    # Clue 1: The person who loves beach vacations is Eric.
    beach = z3.Const('beach', Vacation)
    eric = z3.Const('Eric', Name)
    for i in houses:
        solver.add(z3.Implies(attrs['vacation'][i-1] == beach, attrs['name'][i-1] == eric))
    
    # Clue 2: The person who loves pop music is the person who loves beach vacations.
    pop = z3.Const('pop', MusicGenre)
    for i in houses:
        solver.add(z3.Implies(attrs['music_genre'][i-1] == pop, attrs['vacation'][i-1] == beach))
    
    # Clue 3: The person who loves rock music is the person who loves mystery books.
    rock = z3.Const('rock', MusicGenre)
    mystery = z3.Const('mystery', BookGenre)
    for i in houses:
        solver.add(z3.Implies(attrs['music_genre'][i-1] == rock, attrs['book_genre'][i-1] == mystery))
    
    # Clue 4: The cat lover is not in the second house.
    cat = z3.Const('cat', Animal)
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