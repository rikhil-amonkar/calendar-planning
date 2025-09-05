import json
from z3 import *

def main():
    solver = Solver()
    num_houses = 2
    houses = list(range(num_houses))
    
    # Define variables for each house and category (domain: 0 or 1).
    # For Names: 0 = "Arnold", 1 = "Eric"
    names = [Int(f"name_{i}") for i in houses]
    # For BookGenre: 0 = "mystery", 1 = "science fiction"
    books = [Int(f"book_{i}") for i in houses]
    # For Vacation: 0 = "mountain", 1 = "beach"
    vacations = [Int(f"vacation_{i}") for i in houses]
    # For Animal: 0 = "cat", 1 = "horse"
    animals = [Int(f"animal_{i}") for i in houses]
    # For MusicGenre: 0 = "rock", 1 = "pop"
    music = [Int(f"music_{i}") for i in houses]
    
    # Constrain all variables to be either 0 or 1.
    for var_list in [names, books, vacations, animals, music]:
        for var in var_list:
            solver.add(Or(var == 0, var == 1))
    
    # All-different constraints for each category.
    solver.add(Distinct(names))
    solver.add(Distinct(books))
    solver.add(Distinct(vacations))
    solver.add(Distinct(animals))
    solver.add(Distinct(music))
    
    # Clue 1: "The person who loves beach vacations is Eric."
    # (beach = 1, Eric = 1) so for each house: vacation[i] == 1 if and only if name[i] == 1.
    for i in houses:
        solver.add(vacations[i] == names[i])
    
    # Clue 2: "The person who loves pop music is the person who loves beach vacations."
    # (pop = 1, beach = 1) so for each house: vacation[i] == music[i].
    for i in houses:
        solver.add(vacations[i] == music[i])
    
    # Clue 3: "The person who loves rock music is the person who loves mystery books."
    # (rock = 0, mystery = 0) so for each house: if music is rock then the book is mystery,
    # and vice versa. Since domain is {0,1}, this is equivalent to: book[i] == music[i].
    for i in houses:
        solver.add(books[i] == music[i])
        
    # Clue 5: "The person who loves mystery books is in the first house."
    # House 1 corresponds to index 0.
    solver.add(books[0] == 0)  # mystery is 0
    
    # Clue 4: "The cat lover is not in the second house."
    # Cat is 0 and House 2 corresponds to index 1.
    solver.add(animals[1] != 0)
    
    # Solve the constraints.
    if solver.check() == sat:
        model = solver.model()
        
        # Define mapping dictionaries.
        name_map = {0: "Arnold", 1: "Eric"}
        book_map = {0: "mystery", 1: "science fiction"}
        vacation_map = {0: "mountain", 1: "beach"}
        animal_map = {0: "cat", 1: "horse"}
        music_map = {0: "rock", 1: "pop"}
        
        # Build the solution rows in house order.
        rows = []
        for i in houses:
            house_number = str(i + 1)
            row = [
                house_number,
                name_map[model.evaluate(names[i]).as_long()],
                book_map[model.evaluate(books[i]).as_long()],
                vacation_map[model.evaluate(vacations[i]).as_long()],
                animal_map[model.evaluate(animals[i]).as_long()],
                music_map[model.evaluate(music[i]).as_long()]
            ]
            rows.append(row)
        
        # Create the output JSON structure.
        output = {
            "solution": {
                "header": ["House", "Name", "BookGenre", "Vacation", "Animal", "MusicGenre"],
                "rows": rows
            }
        }
        print(json.dumps(output))
    else:
        print(json.dumps({"solution": "No solution found."}))

if __name__ == '__main__':
    main()