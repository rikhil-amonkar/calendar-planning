from z3 import *

def main():
    # Define datatypes for each attribute
    Name = Datatype('Name')
    Name.declare('Arnold')
    Name.declare('Eric')
    Name = Name.create()
    
    BookGenre = Datatype('BookGenre')
    BookGenre.declare('science_fiction')
    BookGenre.declare('mystery')
    BookGenre = BookGenre.create()
    
    Vacation = Datatype('Vacation')
    Vacation.declare('mountain')
    Vacation.declare('beach')
    Vacation = Vacation.create()
    
    Animal = Datatype('Animal')
    Animal.declare('cat')
    Animal.declare('horse')
    Animal = Animal.create()
    
    MusicGenre = Datatype('MusicGenre')
    MusicGenre.declare('rock')
    MusicGenre.declare('pop')
    MusicGenre = MusicGenre.create()
    
    # Create variables for each house
    name1 = Const('name1', Name)
    book_genre1 = Const('book_genre1', BookGenre)
    vacation1 = Const('vacation1', Vacation)
    animal1 = Const('animal1', Animal)
    music1 = Const('music1', MusicGenre)
    
    name2 = Const('name2', Name)
    book_genre2 = Const('book_genre2', BookGenre)
    vacation2 = Const('vacation2', Vacation)
    animal2 = Const('animal2', Animal)
    music2 = Const('music2', MusicGenre)
    
    s = Solver()
    
    # Each attribute must be unique across houses
    s.add(Distinct(name1, name2))
    s.add(Distinct(book_genre1, book_genre2))
    s.add(Distinct(vacation1, vacation2))
    s.add(Distinct(animal1, animal2))
    s.add(Distinct(music1, music2))
    
    # Clue 1: Beach vacation person is Eric
    s.add(Implies(vacation1 == Vacation.beach, name1 == Name.Eric))
    s.add(Implies(vacation2 == Vacation.beach, name2 == Name.Eric))
    
    # Clue 2: Pop music lover is beach vacation lover
    s.add((music1 == MusicGenre.pop) == (vacation1 == Vacation.beach))
    s.add((music2 == MusicGenre.pop) == (vacation2 == Vacation.beach))
    
    # Clue 3: Rock music lover is mystery book lover
    s.add((music1 == MusicGenre.rock) == (book_genre1 == BookGenre.mystery))
    s.add((music2 == MusicGenre.rock) == (book_genre2 == BookGenre.mystery))
    
    # Clue 4: Cat lover is not in house 2 (so in house 1)
    s.add(animal1 == Animal.cat)
    
    # Clue 5: Mystery book lover is in house 1
    s.add(book_genre1 == BookGenre.mystery)
    
    # Check satisfiability
    if s.check() == sat:
        m = s.model()
        
        # Mapping from Z3 constants to display strings
        name_map = {Name.Arnold: "Arnold", Name.Eric: "Eric"}
        book_genre_map = {BookGenre.science_fiction: "science fiction", BookGenre.mystery: "mystery"}
        vacation_map = {Vacation.mountain: "mountain", Vacation.beach: "beach"}
        animal_map = {Animal.cat: "cat", Animal.horse: "horse"}
        music_map = {MusicGenre.rock: "rock", MusicGenre.pop: "pop"}
        
        # Extract values for house 1
        n1 = name_map[m.eval(name1).as_long()]
        bg1 = book_genre_map[m.eval(book_genre1).as_long()]
        v1 = vacation_map[m.eval(vacation1).as_long()]
        a1 = animal_map[m.eval(animal1).as_long()]
        m1 = music_map[m.eval(music1).as_long()]
        
        # Extract values for house 2
        n2 = name_map[m.eval(name2).as_long()]
        bg2 = book_genre_map[m.eval(book_genre2).as_long()]
        v2 = vacation_map[m.eval(vacation2).as_long()]
        a2 = animal_map[m.eval(animal2).as_long()]
        m2 = music_map[m.eval(music2).as_long()]
        
        # Prepare the solution dictionary
        solution = {
            "solution": {
                "header": ["House", "Name", "BookGenre", "Vacation", "Animal", "MusicGenre"],
                "rows": [
                    ["1", n1, bg1, v1, a1, m1],
                    ["2", n2, bg2, v2, a2, m2]
                ]
            }
        }
        
        # Print as JSON
        import json
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()