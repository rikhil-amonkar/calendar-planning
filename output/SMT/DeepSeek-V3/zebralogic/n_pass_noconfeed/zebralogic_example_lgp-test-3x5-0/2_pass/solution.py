import json
from z3 import *

def main():
    # Create solver
    solver = Solver()
    
    # Define attributes
    houses = [1, 2, 3]
    names = ['Peter', 'Arnold', 'Eric']
    book_genres = ['science fiction', 'mystery', 'romance']
    smoothies = ['watermelon', 'desert', 'cherry']
    birthdays = ['jan', 'april', 'sept']
    heights = ['average', 'very short', 'short']
    
    # Create variables for each attribute per house
    name_vars = [Int(f'name_{i}') for i in houses]
    book_vars = [Int(f'book_{i}') for i in houses]
    smoothie_vars = [Int(f'smoothie_{i}') for i in houses]
    birthday_vars = [Int(f'birthday_{i}') for i in houses]
    height_vars = [Int(f'height_{i}') for i in houses]
    
    # Constraint: all attributes must be within valid range (0-2)
    for i in houses:
        solver.add(And(name_vars[i-1] >= 0, name_vars[i-1] <= 2))
        solver.add(And(book_vars[i-1] >= 0, book_vars[i-1] <= 2))
        solver.add(And(smoothie_vars[i-1] >= 0, smoothie_vars[i-1] <= 2))
        solver.add(And(birthday_vars[i-1] >= 0, birthday_vars[i-1] <= 2))
        solver.add(And(height_vars[i-1] >= 0, height_vars[i-1] <= 2))
    
    # Constraint: all attributes must be unique per house
    solver.add(Distinct(name_vars))
    solver.add(Distinct(book_vars))
    solver.add(Distinct(smoothie_vars))
    solver.add(Distinct(birthday_vars))
    solver.add(Distinct(height_vars))
    
    # Map attribute values to indices
    name_idx = {name: idx for idx, name in enumerate(names)}
    book_idx = {genre: idx for idx, genre in enumerate(book_genres)}
    smoothie_idx = {smoothie: idx for idx, smoothie in enumerate(smoothies)}
    birthday_idx = {month: idx for idx, month in enumerate(birthdays)}
    height_idx = {height: idx for idx, height in enumerate(heights)}
    
    # Clue 1: The person who likes Cherry smoothies is not in the second house.
    solver.add(smoothie_vars[1] != smoothie_idx['cherry'])
    
    # Clue 2: Arnold is the person who loves mystery books.
    # Fixed: Use a simpler approach without ForAll
    for i in range(3):
        solver.add(Implies(name_vars[i] == name_idx['Arnold'], 
                          book_vars[i] == book_idx['mystery']))
        solver.add(Implies(book_vars[i] == book_idx['mystery'], 
                          name_vars[i] == name_idx['Arnold']))
    
    # Clue 3: The person whose birthday is in January is not in the first house.
    solver.add(birthday_vars[0] != birthday_idx['jan'])
    
    # Clue 4: The person who is very short is the person who loves romance books.
    for i in range(3):
        solver.add(Implies(height_vars[i] == height_idx['very short'], 
                          book_vars[i] == book_idx['romance']))
        solver.add(Implies(book_vars[i] == book_idx['romance'], 
                          height_vars[i] == height_idx['very short']))
    
    # Clue 5: The person who loves mystery books is the person whose birthday is in September.
    for i in range(3):
        solver.add(Implies(book_vars[i] == book_idx['mystery'], 
                          birthday_vars[i] == birthday_idx['sept']))
        solver.add(Implies(birthday_vars[i] == birthday_idx['sept'], 
                          book_vars[i] == book_idx['mystery']))
    
    # Clue 6: The person who has an average height is the Desert smoothie lover.
    for i in range(3):
        solver.add(Implies(height_vars[i] == height_idx['average'], 
                          smoothie_vars[i] == smoothie_idx['desert']))
        solver.add(Implies(smoothie_vars[i] == smoothie_idx['desert'], 
                          height_vars[i] == height_idx['average']))
    
    # Clue 7: Eric is in the first house.
    solver.add(name_vars[0] == name_idx['Eric'])
    
    # Clue 8: The Watermelon smoothie lover is the person who is short.
    for i in range(3):
        solver.add(Implies(smoothie_vars[i] == smoothie_idx['watermelon'], 
                          height_vars[i] == height_idx['short']))
        solver.add(Implies(height_vars[i] == height_idx['short'], 
                          smoothie_vars[i] == smoothie_idx['watermelon']))
    
    # Clue 9: The Watermelon smoothie lover is Eric.
    for i in range(3):
        solver.add(Implies(smoothie_vars[i] == smoothie_idx['watermelon'], 
                          name_vars[i] == name_idx['Eric']))
        solver.add(Implies(name_vars[i] == name_idx['Eric'], 
                          smoothie_vars[i] == smoothie_idx['watermelon']))
    
    # Check if solution exists
    if solver.check() == sat:
        model = solver.model()
        
        # Prepare result data
        rows = []
        for i in range(3):
            name_val = model.eval(name_vars[i]).as_long()
            book_val = model.eval(book_vars[i]).as_long()
            smoothie_val = model.eval(smoothie_vars[i]).as_long()
            birthday_val = model.eval(birthday_vars[i]).as_long()
            height_val = model.eval(height_vars[i]).as_long()
            
            row = [
                str(i + 1),
                names[name_val],
                book_genres[book_val],
                smoothies[smoothie_val],
                birthdays[birthday_val],
                heights[height_val]
            ]
            rows.append(row)
        
        # Create JSON output
        result = {
            "solution": {
                "header": ["House", "Name", "BookGenre", "Smoothie", "Birthday", "Height"],
                "rows": rows
            }
        }
        
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()