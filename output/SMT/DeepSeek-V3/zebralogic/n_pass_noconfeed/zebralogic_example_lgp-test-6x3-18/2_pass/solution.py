import z3
import json

def main():
    solver = z3.Solver()
    
    # Define the houses
    n_houses = 6
    houses = list(range(1, n_houses+1))
    
    # Define the attributes
    names = ['Arnold', 'Eric', 'Bob', 'Alice', 'Carol', 'Peter']
    mothers = ['Sarah', 'Holly', 'Janelle', 'Aniya', 'Penny', 'Kailyn']
    pets = ['hamster', 'dog', 'bird', 'cat', 'fish', 'rabbit']
    
    # Create Z3 variables for each attribute per house
    name_vars = [z3.Int(f'name_{i}') for i in houses]
    mother_vars = [z3.Int(f'mother_{i}') for i in houses]
    pet_vars = [z3.Int(f'pet_{i}') for i in houses]
    
    # Constraint: all attributes are within their respective domains
    for i in houses:
        solver.add(z3.And(name_vars[i-1] >= 0, name_vars[i-1] < len(names)))
        solver.add(z3.And(mother_vars[i-1] >= 0, mother_vars[i-1] < len(mothers)))
        solver.add(z3.And(pet_vars[i-1] >= 0, pet_vars[i-1] < len(pets)))
    
    # Constraint: all attributes are distinct within their category
    solver.add(z3.Distinct(name_vars))
    solver.add(z3.Distinct(mother_vars))
    solver.add(z3.Distinct(pet_vars))
    
    # Clue 1: Bob is not in the second house.
    bob_index = names.index('Bob')
    solver.add(name_vars[1] != bob_index)  # house 2 is index 1
    
    # Clue 2: There are two houses between the person who has a cat and the person who owns a rabbit.
    cat_index = pets.index('cat')
    rabbit_index = pets.index('rabbit')
    # Create a constraint that exactly one pair has distance 3
    cat_rabbit_pairs = []
    for i in houses:
        for j in houses:
            if abs(i - j) == 3:
                cat_rabbit_pairs.append(z3.And(pet_vars[i-1] == cat_index, pet_vars[j-1] == rabbit_index))
    solver.add(z3.Or(cat_rabbit_pairs))
    
    # Clue 3: The person who has a cat is directly left of The person whose mother's name is Holly.
    holly_index = mothers.index('Holly')
    for i in range(1, n_houses):
        solver.add(z3.Implies(pet_vars[i-1] == cat_index, mother_vars[i] == holly_index))
    
    # Clue 4: The person with a pet hamster is directly left of the person who owns a rabbit.
    hamster_index = pets.index('hamster')
    for i in range(1, n_houses):
        solver.add(z3.Implies(pet_vars[i-1] == hamster_index, pet_vars[i] == rabbit_index))
    
    # Clue 5: The person who owns a rabbit is Eric.
    eric_index = names.index('Eric')
    for i in houses:
        solver.add(z3.Implies(pet_vars[i-1] == rabbit_index, name_vars[i-1] == eric_index))
    
    # Clue 6: There is one house between the person who owns a dog and the person who has a cat.
    dog_index = pets.index('dog')
    # Create a constraint that exactly one pair has distance 2
    dog_cat_pairs = []
    for i in houses:
        for j in houses:
            if abs(i - j) == 2:
                dog_cat_pairs.append(z3.And(pet_vars[i-1] == dog_index, pet_vars[j-1] == cat_index))
    solver.add(z3.Or(dog_cat_pairs))
    
    # Clue 7: The person who has a cat is The person whose mother's name is Janelle.
    janelle_index = mothers.index('Janelle')
    for i in houses:
        solver.add(z3.Implies(pet_vars[i-1] == cat_index, mother_vars[i-1] == janelle_index))
    
    # Clue 8: Alice is directly left of Carol.
    alice_index = names.index('Alice')
    carol_index = names.index('Carol')
    for i in range(1, n_houses):
        solver.add(z3.Implies(name_vars[i-1] == alice_index, name_vars[i] == carol_index))
    
    # Clue 9: Carol is The person whose mother's name is Aniya.
    aniya_index = mothers.index('Aniya')
    for i in houses:
        solver.add(z3.Implies(name_vars[i-1] == carol_index, mother_vars[i-1] == aniya_index))
    
    # Clue 10: Arnold is the person who has a cat.
    arnold_index = names.index('Arnold')
    for i in houses:
        solver.add(z3.Implies(name_vars[i-1] == arnold_index, pet_vars[i-1] == cat_index))
    
    # Clue 11: The person whose mother's name is Kailyn is the person who owns a rabbit.
    kailyn_index = mothers.index('Kailyn')
    for i in houses:
        solver.add(z3.Implies(mother_vars[i-1] == kailyn_index, pet_vars[i-1] == rabbit_index))
    
    # Clue 12: The person with an aquarium of fish is The person whose mother's name is Sarah.
    fish_index = pets.index('fish')
    sarah_index = mothers.index('Sarah')
    for i in houses:
        solver.add(z3.Implies(pet_vars[i-1] == fish_index, mother_vars[i-1] == sarah_index))
    
    # Check if the constraints are satisfiable
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Create result structure
        result = []
        
        # Extract values from the model
        for i in houses:
            name_val = model.eval(name_vars[i-1]).as_long()
            mother_val = model.eval(mother_vars[i-1]).as_long()
            pet_val = model.eval(pet_vars[i-1]).as_long()
            
            row = {
                "House": str(i),
                "Name": names[name_val],
                "Mother": mothers[mother_val],
                "Pet": pets[pet_val]
            }
            result.append(row)
        
        # Output as JSON
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()