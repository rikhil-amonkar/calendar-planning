import z3
import json

def main():
    # Define enums for attributes
    Name, (Eric, Arnold) = z3.EnumSort('Name', ['Eric', 'Arnold'])
    BookGenre, (science_fiction, mystery) = z3.EnumSort('BookGenre', ['science_fiction', 'mystery'])
    
    # Create variables for each house
    names = [z3.Const(f'name_{i}', Name) for i in range(2)]
    books = [z3.Const(f'book_{i}', BookGenre) for i in range(2)]
    
    solver = z3.Solver()
    
    # Add uniqueness constraints
    solver.add(z3.Distinct(names))
    solver.add(z3.Distinct(books))
    
    # Clue: Eric is directly left of the person who loves mystery books
    solver.add(names[0] == Eric)
    solver.add(books[1] == mystery)
    
    # Check solution
    if solver.check() == z3.sat:
        model = solver.model()
        rows = []
        for i in range(2):
            house_num = str(i + 1)
            name_val = model.eval(names[i])
            book_val = model.eval(books[i])
            
            # Convert Z3 values to strings
            name_str = 'Eric' if name_val == Eric else 'Arnold'
            book_str = 'science fiction' if book_val == science_fiction else 'mystery'
            
            rows.append([house_num, name_str, book_str])
        
        result = {
            "solution": {
                "header": ["House", "Name", "BookGenre"],
                "rows": rows
            }
        }
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == '__main__':
    main()