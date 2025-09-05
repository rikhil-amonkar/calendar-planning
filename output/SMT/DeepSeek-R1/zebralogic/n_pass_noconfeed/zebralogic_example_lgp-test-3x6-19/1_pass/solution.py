import z3
import json

def main():
    # Initialize the solver
    solver = z3.Solver()
    
    # Define the number of houses
    n_houses = 3
    
    # Create enumerations for each attribute type
    NameSort, (Arnold, Eric, Peter) = z3.EnumSort('NameSort', ['Arnold', 'Eric', 'Peter'])
    CigarSort, (pall_mall, blue_master, prince) = z3.EnumSort('CigarSort', ['pall_mall', 'blue_master', 'prince'])
    AnimalSort, (horse, cat, bird) = z3.EnumSort('AnimalSort', ['horse', 'cat', 'bird'])
    ChildrenSort, (Bella, Fred, Meredith) = z3.EnumSort('ChildrenSort', ['Bella', 'Fred', 'Meredith'])
    BookGenreSort, (science_fiction, romance, mystery) = z3.EnumSort('BookGenreSort', ['science_fiction', 'romance', 'mystery'])
    PhoneModelSort, (google_pixel_6, iphone_13, samsung_galaxy_s21) = z3.EnumSort('PhoneModelSort', ['google_pixel_6', 'iphone_13', 'samsung_galaxy_s21'])
    
    # Create variables for each house and each attribute
    names = [z3.Const(f'name_{i}', NameSort) for i in range(n_houses)]
    cigars = [z3.Const(f'cigar_{i}', CigarSort) for i in range(n_houses)]
    animals = [z3.Const(f'animal_{i}', AnimalSort) for i in range(n_houses)]
    children = [z3.Const(f'children_{i}', ChildrenSort) for i in range(n_houses)]
    book_genres = [z3.Const(f'book_genre_{i}', BookGenreSort) for i in range(n_houses)]
    phone_models = [z3.Const(f'phone_model_{i}', PhoneModelSort) for i in range(n_houses)]
    
    # Add constraints that all attributes are distinct
    solver.add(z3.Distinct(names))
    solver.add(z3.Distinct(cigars))
    solver.add(z3.Distinct(animals))
    solver.add(z3.Distinct(children))
    solver.add(z3.Distinct(book_genres))
    solver.add(z3.Distinct(phone_models))
    
    # Clue 1: The person who loves mystery books is the person's child is named Fred.
    for i in range(n_houses):
        solver.add(z3.Implies(book_genres[i] == mystery, children[i] == Fred))
    
    # Clue 2: The cat lover is Eric.
    for i in range(n_houses):
        solver.add(z3.Implies(animals[i] == cat, names[i] == Eric))
    
    # Clue 3: The person partial to Pall Mall is in the second house.
    solver.add(cigars[1] == pall_mall)
    
    # Clue 4: The person who keeps horses is the person's child is named Meredith.
    for i in range(n_houses):
        solver.add(z3.Implies(animals[i] == horse, children[i] == Meredith))
    
    # Clue 5: The person's child is named Bella is the Prince smoker.
    for i in range(n_houses):
        solver.add(z3.Implies(children[i] == Bella, cigars[i] == prince))
    
    # Clue 6: The person who uses an iPhone 13 is directly left of the person who uses a Samsung Galaxy S21.
    for i in range(n_houses - 1):
        solver.add(z3.Implies(phone_models[i] == iphone_13, phone_models[i+1] == samsung_galaxy_s21))
    # Also ensure that if Samsung is in position i, then iPhone must be in i-1 (only one possibility)
    solver.add(z3.Or([z3.And(phone_models[i] == iphone_13, phone_models[i+1] == samsung_galaxy_s21) for i in range(n_houses-1)]))
    
    # Clue 7: The person's child is named Fred is directly left of Arnold.
    for i in range(n_houses - 1):
        solver.add(z3.Implies(children[i] == Fred, names[i+1] == Arnold))
    # Ensure exactly one occurrence of this left-right relationship
    solver.add(z3.Or([z3.And(children[i] == Fred, names[i+1] == Arnold) for i in range(n_houses-1)]))
    
    # Clue 8: Peter is somewhere to the left of Eric.
    # Find indices where Peter and Eric are located
    peter_index = z3.Int('peter_index')
    eric_index = z3.Int('eric_index')
    solver.add(peter_index >= 0, peter_index < n_houses)
    solver.add(eric_index >= 0, eric_index < n_houses)
    for i in range(n_houses):
        solver.add(z3.Implies(names[i] == Peter, peter_index == i))
        solver.add(z3.Implies(names[i] == Eric, eric_index == i))
    solver.add(peter_index < eric_index)
    
    # Clue 9: The person who loves science fiction books is the person who uses a Samsung Galaxy S21.
    for i in range(n_houses):
        solver.add(z3.Implies(book_genres[i] == science_fiction, phone_models[i] == samsung_galaxy_s21))
    
    # Clue 10: The person who loves science fiction books is in the third house.
    solver.add(book_genres[2] == science_fiction)
    
    # Clue 11: The person who loves mystery books is not in the second house.
    solver.add(book_genres[1] != mystery)
    
    # Check if the solver is satisfied and get the model
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Function to get the value of a constant from the model
        def get_value(var, sort_enum):
            return str(model[var]).split('::')[0]
        
        # Prepare the solution dictionary
        solution = {
            "solution": {
                "header": ["House", "Name", "Cigar", "Animal", "Children", "BookGenre", "PhoneModel"],
                "rows": []
            }
        }
        
        # Map house indices to the attribute values
        for i in range(n_houses):
            house_num = str(i+1)
            name_val = get_value(names[i], NameSort)
            cigar_val = get_value(cigars[i], CigarSort).replace('_', ' ')
            animal_val = get_value(animals[i], AnimalSort)
            children_val = get_value(children[i], ChildrenSort)
            book_genre_val = get_value(book_genres[i], BookGenreSort).replace('_', ' ')
            phone_model_val = get_value(phone_models[i], PhoneModelSort).replace('_', ' ')
            
            row = [house_num, name_val, cigar_val, animal_val, children_val, book_genre_val, phone_model_val]
            solution["solution"]["rows"].append(row)
        
        # Output the solution as JSON
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()