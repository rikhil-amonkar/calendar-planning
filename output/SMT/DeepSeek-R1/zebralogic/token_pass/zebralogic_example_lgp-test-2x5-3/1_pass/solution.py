import json
from z3 import *

def main():
    # Define the attributes and their possible values
    names = ['Eric', 'Arnold']
    hobbies = ['gardening', 'photography']
    book_genres = ['science fiction', 'mystery']
    music_genres = ['rock', 'pop']
    birthday_months = ['april', 'sept']
    
    # Create Z3 enums for each attribute type
    Name = Datatype('Name')
    for n in names:
        Name.declare(n)
    Name = Name.create()
    
    Hobby = Datatype('Hobby')
    for h in hobbies:
        Hobby.declare(h)
    Hobby = Hobby.create()
    
    BookGenre = Datatype('BookGenre')
    for b in book_genres:
        BookGenre.declare(b)
    BookGenre = BookGenre.create()
    
    MusicGenre = Datatype('MusicGenre')
    for m in music_genres:
        MusicGenre.declare(m)
    MusicGenre = MusicGenre.create()
    
    Birthday = Datatype('Birthday')
    for bd in birthday_months:
        Birthday.declare(bd)
    Birthday = Birthday.create()
    
    # Create variables for each house's attributes
    house1_name = Const('house1_name', Name)
    house2_name = Const('house2_name', Name)
    house1_hobby = Const('house1_hobby', Hobby)
    house2_hobby = Const('house2_hobby', Hobby)
    house1_book = Const('house1_book', BookGenre)
    house2_book = Const('house2_book', BookGenre)
    house1_music = Const('house1_music', MusicGenre)
    house2_music = Const('house2_music', MusicGenre)
    house1_birthday = Const('house1_birthday', Birthday)
    house2_birthday = Const('house2_birthday', Birthday)
    
    s = Solver()
    
    # Each attribute must have distinct values across houses
    s.add(Distinct(house1_name, house2_name))
    s.add(Distinct(house1_hobby, house2_hobby))
    s.add(Distinct(house1_book, house2_book))
    s.add(Distinct(house1_music, house2_music))
    s.add(Distinct(house1_birthday, house2_birthday))
    
    # Clue 1: The person who loves mystery books is the person who loves rock music.
    s.add(ForAll([house1_book, house2_book, house1_music, house2_music],
                 Implies(Or(house1_book == BookGenre.mystery, house2_book == BookGenre.mystery),
                         And(If(house1_book == BookGenre.mystery, house1_music == MusicGenre.rock, house2_music == MusicGenre.rock)))))
    
    # Clue 2: Arnold is not in the first house.
    s.add(house1_name != Name.Arnold)
    
    # Clue 3: The person who loves mystery books is the person who enjoys gardening.
    s.add(ForAll([house1_book, house2_book, house1_hobby, house2_hobby],
                 Implies(Or(house1_book == BookGenre.mystery, house2_book == BookGenre.mystery),
                         And(If(house1_book == BookGenre.mystery, house1_hobby == Hobby.gardening, house2_hobby == Hobby.gardening)))))
    
    # Clue 4: The person whose birthday is in April is Arnold.
    s.add(ForAll([house1_birthday, house2_birthday, house1_name, house2_name],
                 Implies(Or(house1_birthday == Birthday.april, house2_birthday == Birthday.april),
                         And(If(house1_birthday == Birthday.april, house1_name == Name.Arnold, house2_name == Name.Arnold)))))
    
    # Clue 5: The person who loves mystery books is in the first house.
    s.add(house1_book == BookGenre.mystery)
    
    # Check satisfiability and get the model
    if s.check() == sat:
        m = s.model()
        
        # Helper function to get string representation of Z3 values
        def z3_to_str(val, enum_type):
            for i in range(val.num_children()):
                if val == enum_type.get_constructor(i)():
                    return enum_type.get_constructor(i).name()
            return None
        
        # Collect results for each house
        rows = []
        for house_num in [1, 2]:
            name_var = globals()[f'house{house_num}_name']
            hobby_var = globals()[f'house{house_num}_hobby']
            book_var = globals()[f'house{house_num}_book']
            music_var = globals()[f'house{house_num}_music']
            birthday_var = globals()[f'house{house_num}_birthday']
            
            name_val = z3_to_str(m.eval(name_var), Name)
            hobby_val = z3_to_str(m.eval(hobby_var), Hobby)
            book_val = z3_to_str(m.eval(book_var), BookGenre)
            music_val = z3_to_str(m.eval(music_var), MusicGenre)
            birthday_val = z3_to_str(m.eval(birthday_var), Birthday)
            
            rows.append([str(house_num), name_val, hobby_val, book_val, music_val, birthday_val])
        
        # Create the solution dictionary
        solution = {
            "solution": {
                "header": ["House", "Name", "Hobby", "BookGenre", "MusicGenre", "Birthday"],
                "rows": rows
            }
        }
        
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()