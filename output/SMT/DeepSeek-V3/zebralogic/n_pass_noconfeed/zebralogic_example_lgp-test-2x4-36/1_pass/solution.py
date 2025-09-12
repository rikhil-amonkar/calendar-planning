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
    birthday_months = ['april', 'sept']
    animals = ['horse', 'cat']
    
    # Create variables for each attribute in each house
    name_vars = {h: z3.Int(f'name_{h}') for h in houses}
    book_vars = {h: z3.Int(f'book_{h}') for h in houses}
    birthday_vars = {h: z3.Int(f'birthday_{h}') for h in houses}
    animal_vars = {h: z3.Int(f'animal_{h}') for h in houses}
    
    # Define domains for each attribute type
    name_domain = {0: 'Eric', 1: 'Arnold'}
    book_domain = {0: 'science fiction', 1: 'mystery'}
    birthday_domain = {0: 'april', 1: 'sept'}
    animal_domain = {0: 'horse', 1: 'cat'}
    
    # Constraint: All attributes within their categories must be unique and within domain
    for h in houses:
        solver.add(z3.And(name_vars[h] >= 0, name_vars[h] < len(names)))
        solver.add(z3.And(book_vars[h] >= 0, book_vars[h] < len(book_genres)))
        solver.add(z3.And(birthday_vars[h] >= 0, birthday_vars[h] < len(birthday_months)))
        solver.add(z3.And(animal_vars[h] >= 0, animal_vars[h] < len(animals)))
    
    # Constraint: All names are different
    solver.add(z3.Distinct([name_vars[h] for h in houses]))
    # Constraint: All book genres are different
    solver.add(z3.Distinct([book_vars[h] for h in houses]))
    # Constraint: All birthday months are different
    solver.add(z3.Distinct([birthday_vars[h] for h in houses]))
    # Constraint: All animals are different
    solver.add(z3.Distinct([animal_vars[h] for h in houses]))
    
    # Clue 1: Eric is in the first house
    solver.add(name_vars[1] == 0)  # Eric is index 0
    
    # Clue 2: Eric is the person whose birthday is in September
    # Since Eric is in house 1, birthday in house 1 must be sept (index 1)
    solver.add(birthday_vars[1] == 1)
    
    # Clue 3: The person who loves science fiction books is in the second house
    solver.add(book_vars[2] == 0)  # science fiction is index 0
    
    # Clue 4: The person who keeps horses is the person whose birthday is in September
    # Since birthday in sept is in house 1 (from clue 2), animal in house 1 must be horse (index 0)
    solver.add(animal_vars[1] == 0)
    
    # Check if solution exists
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Prepare result
        header = ["House", "Name", "BookGenre", "Birthday", "Animal"]
        rows = []
        
        for house in sorted(houses):
            name_val = name_domain[model.evaluate(name_vars[house]).as_long()]
            book_val = book_domain[model.evaluate(book_vars[house]).as_long()]
            birthday_val = birthday_domain[model.evaluate(birthday_vars[house]).as_long()]
            animal_val = animal_domain[model.evaluate(animal_vars[house]).as_long()]
            
            rows.append([str(house), name_val, book_val, birthday_val, animal_val])
        
        # Create JSON output
        result = {
            "solution": {
                "header": header,
                "rows": rows
            }
        }
        
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()