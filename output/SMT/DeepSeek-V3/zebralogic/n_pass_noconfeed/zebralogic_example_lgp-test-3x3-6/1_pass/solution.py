import z3
import json

def main():
    solver = z3.Solver()
    
    # Define houses
    houses = [1, 2, 3]
    
    # Define attributes
    names = ['Eric', 'Arnold', 'Peter']
    book_genres = ['mystery', 'science fiction', 'romance']
    vacations = ['mountain', 'beach', 'city']
    
    # Create variables for each attribute per house
    name_vars = [z3.Int(f'name_{h}') for h in houses]
    book_vars = [z3.Int(f'book_{h}') for h in houses]
    vacation_vars = [z3.Int(f'vacation_{h}') for h in houses]
    
    # Constraint: All attributes must be within valid range (0-2)
    for h in houses:
        solver.add(z3.And(name_vars[h-1] >= 0, name_vars[h-1] < len(names)))
        solver.add(z3.And(book_vars[h-1] >= 0, book_vars[h-1] < len(book_genres)))
        solver.add(z3.And(vacation_vars[h-1] >= 0, vacation_vars[h-1] < len(vacations)))
    
    # Constraint: All attributes must be unique within their category
    solver.add(z3.Distinct(name_vars))
    solver.add(z3.Distinct(book_vars))
    solver.add(z3.Distinct(vacation_vars))
    
    # Map attribute values to their indices for easier constraint formulation
    name_to_idx = {name: idx for idx, name in enumerate(names)}
    book_to_idx = {genre: idx for idx, genre in enumerate(book_genres)}
    vacation_to_idx = {vac: idx for idx, vac in enumerate(vacations)}
    
    # Clue 1: Eric is directly left of Arnold
    eric_idx = name_to_idx['Eric']
    arnold_idx = name_to_idx['Arnold']
    for h in [1, 2]:  # Eric can only be in house 1 or 2 if directly left of Arnold
        solver.add(z3.Implies(name_vars[h-1] == eric_idx, name_vars[h] == arnold_idx))
    
    # Clue 2: Peter is somewhere to the right of the person who loves beach vacations
    peter_idx = name_to_idx['Peter']
    beach_idx = vacation_to_idx['beach']
    
    # Find which house has beach vacation
    beach_house = z3.Int('beach_house')
    solver.add(beach_house >= 1, beach_house <= 3)
    for h in houses:
        solver.add(z3.Implies(vacation_vars[h-1] == beach_idx, beach_house == h))
    
    # Peter's house must be greater than beach house
    peter_house = z3.Int('peter_house')
    solver.add(peter_house >= 1, peter_house <= 3)
    for h in houses:
        solver.add(z3.Implies(name_vars[h-1] == peter_idx, peter_house == h))
    
    solver.add(peter_house > beach_house)
    
    # Clue 3: Peter is the person who prefers city breaks
    city_idx = vacation_to_idx['city']
    for h in houses:
        solver.add(z3.Implies(name_vars[h-1] == peter_idx, vacation_vars[h-1] == city_idx))
    
    # Clue 4: The person who loves mystery books is somewhere to the left of the person who loves beach vacations
    mystery_idx = book_to_idx['mystery']
    
    # Find which house has mystery book
    mystery_house = z3.Int('mystery_house')
    solver.add(mystery_house >= 1, mystery_house <= 3)
    for h in houses:
        solver.add(z3.Implies(book_vars[h-1] == mystery_idx, mystery_house == h))
    
    solver.add(mystery_house < beach_house)
    
    # Clue 5: The person who loves science fiction books is the person who loves beach vacations
    scifi_idx = book_to_idx['science fiction']
    for h in houses:
        solver.add(z3.Implies(vacation_vars[h-1] == beach_idx, book_vars[h-1] == scifi_idx))
    
    # Check if solution exists
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Prepare solution data
        solution_data = {
            "solution": {
                "header": ["House", "Name", "BookGenre", "Vacation"],
                "rows": []
            }
        }
        
        # Extract values for each house
        for h in houses:
            name_val = model.evaluate(name_vars[h-1])
            book_val = model.evaluate(book_vars[h-1])
            vacation_val = model.evaluate(vacation_vars[h-1])
            
            # Convert indices to actual values
            name = names[name_val.as_long()]
            book_genre = book_genres[book_val.as_long()]
            vacation_type = vacations[vacation_val.as_long()]
            
            solution_data["solution"]["rows"].append([
                str(h), name, book_genre, vacation_type
            ])
        
        # Output as JSON
        print(json.dumps(solution_data, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()