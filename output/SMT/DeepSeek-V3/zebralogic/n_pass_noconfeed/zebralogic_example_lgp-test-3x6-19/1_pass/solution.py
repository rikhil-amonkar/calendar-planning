import z3
import json

def main():
    solver = z3.Solver()
    
    # Define the houses
    houses = [1, 2, 3]
    
    # Define attributes with their possible values
    names = ['Arnold', 'Eric', 'Peter']
    cigars = ['pall mall', 'blue master', 'prince']
    animals = ['horse', 'cat', 'bird']
    children = ['Bella', 'Fred', 'Meredith']
    book_genres = ['science fiction', 'romance', 'mystery']
    phone_models = ['google pixel 6', 'iphone 13', 'samsung galaxy s21']
    
    # Create Z3 variables for each attribute in each house
    name_vars = [z3.Int(f'name_{h}') for h in houses]
    cigar_vars = [z3.Int(f'cigar_{h}') for h in houses]
    animal_vars = [z3.Int(f'animal_{h}') for h in houses]
    child_vars = [z3.Int(f'child_{h}') for h in houses]
    book_vars = [z3.Int(f'book_{h}') for h in houses]
    phone_vars = [z3.Int(f'phone_{h}') for h in houses]
    
    # Define the domain for each attribute (0-indexed)
    name_domain = {names[i]: i for i in range(3)}
    cigar_domain = {cigars[i]: i for i in range(3)}
    animal_domain = {animals[i]: i for i in range(3)}
    child_domain = {children[i]: i for i in range(3)}
    book_domain = {book_genres[i]: i for i in range(3)}
    phone_domain = {phone_models[i]: i for i in range(3)}
    
    # Each attribute must be one of the possible values
    for h in houses:
        solver.add(z3.And(name_vars[h-1] >= 0, name_vars[h-1] < 3))
        solver.add(z3.And(cigar_vars[h-1] >= 0, cigar_vars[h-1] < 3))
        solver.add(z3.And(animal_vars[h-1] >= 0, animal_vars[h-1] < 3))
        solver.add(z3.And(child_vars[h-1] >= 0, child_vars[h-1] < 3))
        solver.add(z3.And(book_vars[h-1] >= 0, book_vars[h-1] < 3))
        solver.add(z3.And(phone_vars[h-1] >= 0, phone_vars[h-1] < 3))
    
    # All attributes must be distinct within their category
    solver.add(z3.Distinct(name_vars))
    solver.add(z3.Distinct(cigar_vars))
    solver.add(z3.Distinct(animal_vars))
    solver.add(z3.Distinct(child_vars))
    solver.add(z3.Distinct(book_vars))
    solver.add(z3.Distinct(phone_vars))
    
    # Clue 1: The person who loves mystery books is the person's child is named Fred.
    for h in houses:
        solver.add(z3.Implies(book_vars[h-1] == book_domain['mystery'], 
                             child_vars[h-1] == child_domain['Fred']))
    
    # Clue 2: The cat lover is Eric.
    for h in houses:
        solver.add(z3.Implies(animal_vars[h-1] == animal_domain['cat'], 
                             name_vars[h-1] == name_domain['Eric']))
    
    # Clue 3: The person partial to Pall Mall is in the second house.
    solver.add(cigar_vars[1] == cigar_domain['pall mall'])
    
    # Clue 4: The person who keeps horses is the person's child is named Meredith.
    for h in houses:
        solver.add(z3.Implies(animal_vars[h-1] == animal_domain['horse'], 
                             child_vars[h-1] == child_domain['Meredith']))
    
    # Clue 5: The person's child is named Bella is the Prince smoker.
    for h in houses:
        solver.add(z3.Implies(child_vars[h-1] == child_domain['Bella'], 
                             cigar_vars[h-1] == cigar_domain['prince']))
    
    # Clue 6: The person who uses an iPhone 13 is directly left of the person who uses a Samsung Galaxy S21.
    solver.add(phone_vars[0] == phone_domain['iphone 13'])
    solver.add(phone_vars[1] == phone_domain['samsung galaxy s21'])
    
    # Clue 7: The person's child is named Fred is directly left of Arnold.
    for h in range(1, 3):
        solver.add(z3.Implies(child_vars[h-1] == child_domain['Fred'], 
                             name_vars[h] == name_domain['Arnold']))
    
    # Clue 8: Peter is somewhere to the left of Eric.
    peter_pos = z3.Int('peter_pos')
    eric_pos = z3.Int('eric_pos')
    solver.add(peter_pos >= 0, peter_pos < 3)
    solver.add(eric_pos >= 0, eric_pos < 3)
    solver.add(peter_pos < eric_pos)
    
    for h in houses:
        solver.add(z3.Implies(name_vars[h-1] == name_domain['Peter'], peter_pos == h-1))
        solver.add(z3.Implies(name_vars[h-1] == name_domain['Eric'], eric_pos == h-1))
    
    # Clue 9: The person who loves science fiction books is the person who uses a Samsung Galaxy S21.
    for h in houses:
        solver.add(z3.Implies(book_vars[h-1] == book_domain['science fiction'], 
                             phone_vars[h-1] == phone_domain['samsung galaxy s21']))
    
    # Clue 10: The person who loves science fiction books is in the third house.
    solver.add(book_vars[2] == book_domain['science fiction'])
    
    # Clue 11: The person who loves mystery books is not in the second house.
    solver.add(book_vars[1] != book_domain['mystery'])
    
    # Check if the constraints are satisfiable
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Create result dictionary
        result = {
            "solution": {
                "header": ["House", "Name", "Cigar", "Animal", "Children", "BookGenre", "PhoneModel"],
                "rows": []
            }
        }
        
        # Helper function to get attribute value from model
        def get_attr_value(var_list, domain, index):
            val = model[var_list[index]].as_long()
            for k, v in domain.items():
                if v == val:
                    return k
            return None
        
        # Populate the rows
        for h in houses:
            row = [
                str(h),
                get_attr_value(name_vars, name_domain, h-1),
                get_attr_value(cigar_vars, cigar_domain, h-1),
                get_attr_value(animal_vars, animal_domain, h-1),
                get_attr_value(child_vars, child_domain, h-1),
                get_attr_value(book_vars, book_domain, h-1),
                get_attr_value(phone_vars, phone_domain, h-1)
            ]
            result["solution"]["rows"].append(row)
        
        # Output as JSON
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()