import json
from z3 import *

def main():
    # Create solver
    solver = Solver()
    
    # Define enums for each category
    Name = Datatype('Name')
    Name.declare('Eric')
    Name.declare('Peter')
    Name.declare('Arnold')
    Name = Name.create()
    
    Cigar = Datatype('Cigar')
    Cigar.declare('blue_master')
    Cigar.declare('prince')
    Cigar.declare('pall_mall')
    Cigar = Cigar.create()
    
    Hobby = Datatype('Hobby')
    Hobby.declare('photography')
    Hobby.declare('gardening')
    Hobby.declare('cooking')
    Hobby = Hobby.create()
    
    Education = Datatype('Education')
    Education.declare('high_school')
    Education.declare('associate')
    Education.declare('bachelor')
    Education = Education.create()
    
    Drink = Datatype('Drink')
    Drink.declare('tea')
    Drink.declare('milk')
    Drink.declare('water')
    Drink = Drink.create()
    
    # Create variables for each house's attributes
    names = [Const(f'name_{i}', Name) for i in range(1,4)]
    cigars = [Const(f'cigar_{i}', Cigar) for i in range(1,4)]
    hobbies = [Const(f'hobby_{i}', Hobby) for i in range(1,4)]
    educations = [Const(f'education_{i}', Education) for i in range(1,4)]
    drinks = [Const(f'drink_{i}', Drink) for i in range(1,4)]
    
    # Add uniqueness constraints
    solver.add(Distinct(names))
    solver.add(Distinct(cigars))
    solver.add(Distinct(hobbies))
    solver.add(Distinct(educations))
    solver.add(Distinct(drinks))
    
    # Clue 1: The person partial to Pall Mall is Peter.
    for i in range(3):
        solver.add(Implies(cigars[i] == Cigar.pall_mall, names[i] == Name.Peter))
    
    # Clue 2: The person who likes milk is directly left of the person with a high school diploma.
    for i in range(2):
        solver.add(Implies(drinks[i] == Drink.milk, educations[i+1] == Education.high_school))
    solver.add(Not(Or(drinks[2] == Drink.milk)))  # Milk can't be in house 3
    
    # Clue 3: Eric is the tea drinker.
    for i in range(3):
        solver.add(Implies(names[i] == Name.Eric, drinks[i] == Drink.tea))
    
    # Clue 4: Arnold and the Prince smoker are next to each other.
    for i in range(3):
        for j in range(3):
            if abs(i-j) == 1:
                solver.add(Implies(names[i] == Name.Arnold, cigars[j] == Cigar.prince))
                solver.add(Implies(cigars[i] == Cigar.prince, names[j] == Name.Arnold))
    
    # Clue 5: The person who enjoys gardening is somewhere to the left of the Prince smoker.
    for i in range(3):
        for j in range(3):
            if i < j:
                solver.add(Implies(hobbies[i] == Hobby.gardening, cigars[j] == Cigar.prince))
    
    # Clue 6: The person who likes milk is the person with an associate's degree.
    for i in range(3):
        solver.add(Implies(drinks[i] == Drink.milk, educations[i] == Education.associate))
    
    # Clue 7: The person with a bachelor's degree is directly left of the photography enthusiast.
    for i in range(2):
        solver.add(Implies(educations[i] == Education.bachelor, hobbies[i+1] == Hobby.photography))
    solver.add(Not(Or(educations[2] == Education.bachelor)))  # Bachelor can't be in house 3
    
    # Check and get solution
    if solver.check() == sat:
        model = solver.model()
        
        # Map house attributes
        result = []
        for i in range(3):
            house = i+1
            name_val = model.eval(names[i])
            cigar_val = model.eval(cigars[i])
            hobby_val = model.eval(hobbies[i])
            education_val = model.eval(educations[i])
            drink_val = model.eval(drinks[i])
            
            # Convert to string names
            name_str = str(name_val).split('!')[0]
            cigar_str = str(cigar_val).split('!')[0]
            hobby_str = str(hobby_val).split('!')[0]
            education_str = str(education_val).split('!')[0]
            drink_str = str(drink_val).split('!')[0]
            
            result.append([str(house), name_str, cigar_str, hobby_str, education_str, drink_str])
        
        # Format output
        output = {
            "solution": {
                "header": ["House", "Name", "Cigar", "Hobby", "Education", "Drink"],
                "rows": result
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()