import json
from z3 import *

def main():
    solver = Solver()
    
    # There are 2 houses, indexed 0 and 1 (which correspond to House 1 and House 2)
    house_count = 2
    houses = range(house_count)
    
    # Mappings for attributes:
    # Names: Eric = 0, Arnold = 1
    names = ["Eric", "Arnold"]
    # Hobbies: gardening = 0, photography = 1
    hobbies = ["gardening", "photography"]
    # BookGenres: mystery = 0, science fiction = 1
    book_genres = ["mystery", "science fiction"]
    # MusicGenres: rock = 0, pop = 1
    music_genres = ["rock", "pop"]
    # Birthdays: april = 0, sept = 1
    birthdays = ["april", "sept"]
    
    # Create variables for each house attribute as integer variables (domain 0..1)
    name_vars = [Int(f"name_{i}") for i in houses]
    hobby_vars = [Int(f"hobby_{i}") for i in houses]
    book_vars = [Int(f"book_{i}") for i in houses]
    music_vars = [Int(f"music_{i}") for i in houses]
    birthday_vars = [Int(f"birthday_{i}") for i in houses]
    
    # Domain constraints: each variable must be either 0 or 1
    for i in houses:
        solver.add(Or(name_vars[i] == 0, name_vars[i] == 1))
        solver.add(Or(hobby_vars[i] == 0, hobby_vars[i] == 1))
        solver.add(Or(book_vars[i] == 0, book_vars[i] == 1))
        solver.add(Or(music_vars[i] == 0, music_vars[i] == 1))
        solver.add(Or(birthday_vars[i] == 0, birthday_vars[i] == 1))
    
    # All different constraints across houses for each attribute.
    solver.add(Distinct(name_vars))
    solver.add(Distinct(hobby_vars))
    solver.add(Distinct(book_vars))
    solver.add(Distinct(music_vars))
    solver.add(Distinct(birthday_vars))
    
    # Clue 5: The person who loves mystery books is in the first house.
    # House 1 is index 0, and mystery is encoded as 0.
    solver.add(book_vars[0] == 0)
    
    # Clue 2: Arnold is not in the first house.
    # Arnold is encoded as 1.
    solver.add(name_vars[0] != 1)
    
    # Clue 1: The person who loves mystery books is the person who loves rock music.
    # This implies for each house: if book genre is mystery (0) then music genre is rock (0), and vice versa.
    for i in houses:
        solver.add(Implies(book_vars[i] == 0, music_vars[i] == 0))
        solver.add(Implies(music_vars[i] == 0, book_vars[i] == 0))
    
    # Clue 3: The person who loves mystery books is the person who enjoys gardening.
    # This implies for each house: if book genre is mystery (0) then hobby is gardening (0), and vice versa.
    for i in houses:
        solver.add(Implies(book_vars[i] == 0, hobby_vars[i] == 0))
        solver.add(Implies(hobby_vars[i] == 0, book_vars[i] == 0))
    
    # Clue 4: The person whose birthday is in April is Arnold.
    # April is encoded as 0 and Arnold as 1.
    for i in houses:
        solver.add(Implies(birthday_vars[i] == 0, name_vars[i] == 1))
        solver.add(Implies(name_vars[i] == 1, birthday_vars[i] == 0))
    
    # Solve the SMT problem
    if solver.check() == sat:
        model = solver.model()
        result = {
            "solution": {
                "header": ["House", "Name", "Hobby", "BookGenre", "MusicGenre", "Birthday"],
                "rows": []
            }
        }
        for i in houses:
            house_number = str(i + 1)
            name_val = names[model[name_vars[i]].as_long()]
            hobby_val = hobbies[model[hobby_vars[i]].as_long()]
            book_val = book_genres[model[book_vars[i]].as_long()]
            music_val = music_genres[model[music_vars[i]].as_long()]
            birthday_val = birthdays[model[birthday_vars[i]].as_long()]
            result["solution"]["rows"].append([house_number, name_val, hobby_val, book_val, music_val, birthday_val])
        print(json.dumps(result))
    else:
        print(json.dumps({"solution": "No solution found"}))

if __name__ == "__main__":
    main()