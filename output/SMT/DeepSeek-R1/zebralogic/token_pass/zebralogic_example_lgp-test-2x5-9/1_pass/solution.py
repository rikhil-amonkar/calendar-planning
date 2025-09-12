from z3 import *
import json

def main():
    solver = Solver()
    
    # Define attributes and their possible values
    Name, (Arnold, Eric) = EnumSort('Name', ['Arnold', 'Eric'])
    BookGenre, (science_fiction, mystery) = EnumSort('BookGenre', ['science fiction', 'mystery'])
    Vacation, (mountain, beach) = EnumSort('Vacation', ['mountain', 'beach'])
    Animal, (cat, horse) = EnumSort('Animal', ['cat', 'horse'])
    MusicGenre, (rock, pop) = EnumSort('MusicGenre', ['rock', 'pop'])
    
    # Create variables for each house
    name1, name2 = Const('name1', Name), Const('name2', Name)
    book1, book2 = Const('book1', BookGenre), Const('book2', BookGenre)
    vacation1, vacation2 = Const('vacation1', Vacation), Const('vacation2', Vacation)
    animal1, animal2 = Const('animal1', Animal), Const('animal2', Animal)
    music1, music2 = Const('music1', MusicGenre), Const('music2', MusicGenre)
    
    # All attributes must be unique per category
    solver.add(Distinct(name1, name2))
    solver.add(Distinct(book1, book2))
    solver.add(Distinct(vacation1, vacation2))
    solver.add(Distinct(animal1, animal2))
    solver.add(Distinct(music1, music2))
    
    # Apply clues
    solver.add(vacation1 == beach)  # Clue 1 and 5 imply beach vacations in house 1
    solver.add(name1 == Eric)       # Clue 1: Beach vacation is Eric
    solver.add(music1 == pop)       # Clue 2: Pop music is beach vacation (house 1)
    solver.add(book1 == mystery)    # Clue 5: Mystery books in first house
    solver.add(music1 == rock)      # Clue 3: Rock music is mystery books (both in house 1)
    solver.add(animal1 == cat)      # Clue 4: Cat not in second house -> must be in first
    
    # Check solution and output
    if solver.check() == sat:
        model = solver.model()
        
        # Convert model values to strings
        def get_value(var):
            return str(model.eval(var))
        
        rows = [
            ["1", get_value(name1), get_value(book1), get_value(vacation1), get_value(animal1), get_value(music1)],
            ["2", get_value(name2), get_value(book2), get_value(vacation2), get_value(animal2), get_value(music2)]
        ]
        
        solution = {
            "solution": {
                "header": ["House", "Name", "BookGenre", "Vacation", "Animal", "MusicGenre"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()