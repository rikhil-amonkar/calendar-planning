import z3
import json

def main():
    # Define the sorts for attributes and unpack the constants
    Name, (Eric, Arnold) = z3.EnumSort('Name', ['Eric', 'Arnold'])
    BookGenre, (ScienceFiction, Mystery) = z3.EnumSort('BookGenre', ['science fiction', 'mystery'])
    
    # Create variables for each house's attributes using the unpacked sorts
    names = [z3.Const(f'name_{i}', Name) for i in range(1, 3)]
    books = [z3.Const(f'book_{i}', BookGenre) for i in range(1, 3)]
    
    solver = z3.Solver()
    
    # All names are distinct
    solver.add(z3.Distinct(names))
    
    # All book genres are distinct
    solver.add(z3.Distinct(books))
    
    # Clue 1: Eric is directly left of the person who loves mystery books
    # Since there are only 2 houses, Eric must be in house 1 and mystery in house 2
    solver.add(names[0] == Eric)
    solver.add(books[1] == Mystery)
    
    # Check for solution
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Prepare results
        rows = []
        for i in range(2):
            house_num = str(i+1)
            name_val = str(model.eval(names[i]))
            book_val = str(model.eval(books[i]))
            rows.append([house_num, name_val, book_val])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "BookGenre"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print('No solution found')

if __name__ == '__main__':
    main()