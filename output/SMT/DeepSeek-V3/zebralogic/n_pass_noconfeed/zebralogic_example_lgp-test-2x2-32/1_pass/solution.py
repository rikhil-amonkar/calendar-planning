import z3
import json

def main():
    # Create solver
    solver = z3.Solver()
    
    # Define houses
    houses = [1, 2]
    
    # Define attributes
    names = ['Eric', 'Arnold']
    book_genres = ['science fiction', 'mystery']
    
    # Create variables for each attribute per house
    name_vars = {}
    book_vars = {}
    
    for house in houses:
        name_vars[house] = z3.Int(f'name_{house}')
        book_vars[house] = z3.Int(f'book_{house}')
    
    # Constraint: All names are distinct and within valid range
    solver.add(z3.Distinct([name_vars[house] for house in houses]))
    for house in houses:
        solver.add(name_vars[house] >= 0, name_vars[house] < len(names))
    
    # Constraint: All book genres are distinct and within valid range
    solver.add(z3.Distinct([book_vars[house] for house in houses]))
    for house in houses:
        solver.add(book_vars[house] >= 0, book_vars[house] < len(book_genres))
    
    # Clue 1: Eric is directly left of the person who loves mystery books
    eric_index = names.index('Eric')
    mystery_index = book_genres.index('mystery')
    
    # Eric in house 1 and mystery lover in house 2
    solver.add(z3.Or(
        z3.And(name_vars[1] == eric_index, book_vars[2] == mystery_index)
    ))
    
    # Check if solution exists
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Prepare solution data
        solution_data = {
            "solution": {
                "header": ["House", "Name", "BookGenre"],
                "rows": []
            }
        }
        
        for house in sorted(houses):
            name_val = model.evaluate(name_vars[house]).as_long()
            book_val = model.evaluate(book_vars[house]).as_long()
            
            row = [
                str(house),
                names[name_val],
                book_genres[book_val]
            ]
            solution_data["solution"]["rows"].append(row)
        
        # Output as JSON
        print(json.dumps(solution_data, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()