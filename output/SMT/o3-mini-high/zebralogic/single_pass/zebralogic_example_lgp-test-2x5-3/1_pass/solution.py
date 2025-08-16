from z3 import *
import json

def main():
    solver = Solver()
    num_houses = 2

    # We use integers 0 and 1 to represent the two possible values for each attribute.
    # Mappings:
    # Names: 0 -> "Arnold", 1 -> "Eric"
    # Hobbies: 0 -> "gardening", 1 -> "photography"
    # BookGenre: 0 -> "mystery", 1 -> "science fiction"
    # MusicGenre: 0 -> "rock", 1 -> "pop"
    # Birthday: 0 -> "april", 1 -> "sept"
    names = [Int(f"name_{i}") for i in range(num_houses)]
    hobbies = [Int(f"hobby_{i}") for i in range(num_houses)]
    bookgenres = [Int(f"book_{i}") for i in range(num_houses)]
    musicgenres = [Int(f"music_{i}") for i in range(num_houses)]
    birthdays = [Int(f"birthday_{i}") for i in range(num_houses)]
    
    # Each variable must be either 0 or 1.
    all_vars = names + hobbies + bookgenres + musicgenres + birthdays
    for var in all_vars:
        solver.add(Or(var == 0, var == 1))
    
    # All houses have a unique value for each attribute.
    solver.add(Distinct(names))
    solver.add(Distinct(hobbies))
    solver.add(Distinct(bookgenres))
    solver.add(Distinct(musicgenres))
    solver.add(Distinct(birthdays))
    
    # Clue 5: "The person who loves mystery books is in the first house."
    # Map mystery to 0. So the first house (house index 0) has mystery.
    solver.add(bookgenres[0] == 0)
    
    # Clue 1: "The person who loves mystery books is the person who loves rock music."
    # Map rock to 0. For each house, bookgenre == 0 if and only if musicgenre == 0.
    for i in range(num_houses):
        solver.add(Implies(bookgenres[i] == 0, musicgenres[i] == 0))
        solver.add(Implies(musicgenres[i] == 0, bookgenres[i] == 0))
    
    # Clue 3: "The person who loves mystery books is the person who enjoys gardening."
    # Map gardening to 0.
    for i in range(num_houses):
        solver.add(Implies(bookgenres[i] == 0, hobbies[i] == 0))
    
    # Clue 2: "Arnold is not in the first house."
    # Arnold is mapped to 0, so the first house's name must not be 0 => it must be "Eric" (mapped to 1).
    solver.add(names[0] != 0)
    
    # Clue 4: "The person whose birthday is in April is Arnold."
    # Map April to 0 and Sept to 1.
    # This means for each house, if the person is Arnold (0) then birthday is April (0),
    # and if the person is not Arnold then the birthday is Sept (1).
    for i in range(num_houses):
        solver.add(If(names[i] == 0, birthdays[i] == 0, birthdays[i] == 1))
    
    if solver.check() == sat:
        model = solver.model()
        # Mapping integer values back to the strings.
        name_map = {0: "Arnold", 1: "Eric"}
        hobby_map = {0: "gardening", 1: "photography"}
        book_map = {0: "mystery", 1: "science fiction"}
        music_map = {0: "rock", 1: "pop"}
        birthday_map = {0: "april", 1: "sept"}
        
        rows = []
        for i in range(num_houses):
            house_number = str(i + 1)
            name_val = model.evaluate(names[i]).as_long()
            hobby_val = model.evaluate(hobbies[i]).as_long()
            book_val = model.evaluate(bookgenres[i]).as_long()
            music_val = model.evaluate(musicgenres[i]).as_long()
            birthday_val = model.evaluate(birthdays[i]).as_long()
            row = [
                house_number,
                name_map[name_val],
                hobby_map[hobby_val],
                book_map[book_val],
                music_map[music_val],
                birthday_map[birthday_val]
            ]
            rows.append(row)
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Hobby", "BookGenre", "MusicGenre", "Birthday"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == '__main__':
    main()