import json
from z3 import *

def main():
    # Initialize solver
    solver = Solver()
    
    # Define mappings for attributes
    name_map = {0: 'Eric', 1: 'Arnold', 2: 'Peter'}
    smoothie_map = {0: 'desert', 1: 'watermelon', 2: 'cherry'}
    book_map = {0: 'science fiction', 1: 'romance', 2: 'mystery'}
    
    # Create variables for each house (3 houses)
    names = [Int(f'name_{i}') for i in range(3)]
    smoothies = [Int(f'smoothie_{i}') for i in range(3)]
    books = [Int(f'book_{i}') for i in range(3)]
    
    # Add constraints for each variable to be in range [0, 2]
    for i in range(3):
        solver.add(And(names[i] >= 0, names[i] <= 2))
        solver.add(And(smoothies[i] >= 0, smoothies[i] <= 2))
        solver.add(And(books[i] >= 0, books[i] <= 2))
    
    # All names, smoothies, and books are distinct
    solver.add(Distinct(names))
    solver.add(Distinct(smoothies))
    solver.add(Distinct(books))
    
    # Clue 1: Cherry smoothie left of mystery book
    cherry_house = If(smoothies[0] == 2, 1, If(smoothies[1] == 2, 2, 3))
    mystery_house = If(books[0] == 2, 1, If(books[1] == 2, 2, 3))
    solver.add(cherry_house < mystery_house)
    
    # Clue 2: Arnold loves mystery books
    for i in range(3):
        solver.add(Implies(books[i] == 2, names[i] == 1))
    
    # Clue 3: Science fiction not in first house
    solver.add(books[0] != 0)
    
    # Clue 4: Desert smoothie directly left of mystery book
    desert_house = If(smoothies[0] == 0, 1, If(smoothies[1] == 0, 2, 3))
    solver.add(desert_house + 1 == mystery_house)
    
    # Clue 5: Peter in first house
    solver.add(names[0] == 2)
    
    # Check satisfiability
    if solver.check() == sat:
        model = solver.model()
        
        # Extract values from model
        solution_rows = []
        for i in range(3):
            name_val = model.eval(names[i]).as_long()
            smoothie_val = model.eval(smoothies[i]).as_long()
            book_val = model.eval(books[i]).as_long()
            
            row = [
                str(i+1),
                name_map[name_val],
                smoothie_map[smoothie_val],
                book_map[book_val]
            ]
            solution_rows.append(row)
        
        # Create JSON output
        output = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "BookGenre"],
                "rows": solution_rows
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()