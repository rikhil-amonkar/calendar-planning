import z3
import json

def main():
    solver = z3.Solver()
    
    # Define the houses
    houses = [1, 2]
    
    # Define attributes
    names = ['Eric', 'Arnold']
    hobbies = ['gardening', 'photography']
    book_genres = ['science fiction', 'mystery']
    music_genres = ['rock', 'pop']
    birthday_months = ['april', 'sept']
    
    # Create variables for each attribute per house
    name_vars = {house: z3.Int(f'name_{house}') for house in houses}
    hobby_vars = {house: z3.Int(f'hobby_{house}') for house in houses}
    book_vars = {house: z3.Int(f'book_{house}') for house in houses}
    music_vars = {house: z3.Int(f'music_{house}') for house in houses}
    birthday_vars = {house: z3.Int(f'birthday_{house}') for house in houses}
    
    # Define domains for each attribute
    name_domain = {0: 'Eric', 1: 'Arnold'}
    hobby_domain = {0: 'gardening', 1: 'photography'}
    book_domain = {0: 'science fiction', 1: 'mystery'}
    music_domain = {0: 'rock', 1: 'pop'}
    birthday_domain = {0: 'april', 1: 'sept'}
    
    # All attributes must be within their respective domains
    for house in houses:
        solver.add(z3.And(name_vars[house] >= 0, name_vars[house] < len(names)))
        solver.add(z3.And(hobby_vars[house] >= 0, hobby_vars[house] < len(hobbies)))
        solver.add(z3.And(book_vars[house] >= 0, book_vars[house] < len(book_genres)))
        solver.add(z3.And(music_vars[house] >= 0, music_vars[house] < len(music_genres)))
        solver.add(z3.And(birthday_vars[house] >= 0, birthday_vars[house] < len(birthday_months)))
    
    # All attributes must be unique per house
    solver.add(z3.Distinct([name_vars[house] for house in houses]))
    solver.add(z3.Distinct([hobby_vars[house] for house in houses]))
    solver.add(z3.Distinct([book_vars[house] for house in houses]))
    solver.add(z3.Distinct([music_vars[house] for house in houses]))
    solver.add(z3.Distinct([birthday_vars[house] for house in houses]))
    
    # Clue 1: The person who loves mystery books is the person who loves rock music.
    for house in houses:
        solver.add(z3.Implies(book_vars[house] == 1, music_vars[house] == 0))
        solver.add(z3.Implies(music_vars[house] == 0, book_vars[house] == 1))
    
    # Clue 2: Arnold is not in the first house.
    solver.add(name_vars[1] != 1)  # Arnold is index 1
    
    # Clue 3: The person who loves mystery books is the person who enjoys gardening.
    for house in houses:
        solver.add(z3.Implies(book_vars[house] == 1, hobby_vars[house] == 0))
        solver.add(z3.Implies(hobby_vars[house] == 0, book_vars[house] == 1))
    
    # Clue 4: The person whose birthday is in April is Arnold.
    for house in houses:
        solver.add(z3.Implies(birthday_vars[house] == 0, name_vars[house] == 1))
        solver.add(z3.Implies(name_vars[house] == 1, birthday_vars[house] == 0))
    
    # Clue 5: The person who loves mystery books is in the first house.
    solver.add(book_vars[1] == 1)
    
    # Check if the problem is satisfiable
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Prepare the solution
        solution = {
            "solution": {
                "header": ["House", "Name", "Hobby", "BookGenre", "MusicGenre", "Birthday"],
                "rows": []
            }
        }
        
        for house in sorted(houses):
            name_val = model.evaluate(name_vars[house]).as_long()
            hobby_val = model.evaluate(hobby_vars[house]).as_long()
            book_val = model.evaluate(book_vars[house]).as_long()
            music_val = model.evaluate(music_vars[house]).as_long()
            birthday_val = model.evaluate(birthday_vars[house]).as_long()
            
            row = [
                str(house),
                name_domain[name_val],
                hobby_domain[hobby_val],
                book_domain[book_val],
                music_domain[music_val],
                birthday_domain[birthday_val]
            ]
            solution["solution"]["rows"].append(row)
        
        print(json.dumps(solution, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()