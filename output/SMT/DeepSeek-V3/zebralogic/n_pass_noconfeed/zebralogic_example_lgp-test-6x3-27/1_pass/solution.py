from z3 import *
import json

def main():
    # Create solver
    solver = Solver()
    
    # Define houses
    n_houses = 6
    houses = list(range(1, n_houses + 1))
    
    # Define attributes
    names = ['Alice', 'Arnold', 'Eric', 'Peter', 'Bob', 'Carol']
    occupations = ['engineer', 'artist', 'doctor', 'teacher', 'nurse', 'lawyer']
    car_models = ['chevrolet silverado', 'ford f150', 'honda civic', 'toyota camry', 'bmw 3 series', 'tesla model 3']
    
    # Create variables for each attribute per house
    name_vars = [Int(f'name_{i}') for i in houses]
    occupation_vars = [Int(f'occupation_{i}') for i in houses]
    car_vars = [Int(f'car_{i}') for i in houses]
    
    # Define domains for variables
    for i in houses:
        solver.add(And(name_vars[i-1] >= 0, name_vars[i-1] < len(names)))
        solver.add(And(occupation_vars[i-1] >= 0, occupation_vars[i-1] < len(occupations)))
        solver.add(And(car_vars[i-1] >= 0, car_vars[i-1] < len(car_models)))
    
    # All attributes are distinct per house
    solver.add(Distinct(name_vars))
    solver.add(Distinct(occupation_vars))
    solver.add(Distinct(car_vars))
    
    # Create mapping from attribute values to indices
    name_to_idx = {name: idx for idx, name in enumerate(names)}
    occupation_to_idx = {occupation: idx for idx, occupation in enumerate(occupations)}
    car_to_idx = {car: idx for idx, car in enumerate(car_models)}
    
    # Clue 1: The person who owns a Ford F-150 is in the fifth house.
    solver.add(car_vars[4] == car_to_idx['ford f150'])
    
    # Clue 2: The person who owns a Chevrolet Silverado is not in the second house.
    solver.add(car_vars[1] != car_to_idx['chevrolet silverado'])
    
    # Clue 3: The person who owns a Honda Civic and Peter are next to each other.
    peter_house = Int('peter_house')
    solver.add(peter_house >= 1, peter_house <= 6)
    solver.add(Or([And(name_vars[i] == name_to_idx['Peter'], peter_house == i+1) for i in range(6)]))
    
    honda_civic_house = Int('honda_civic_house')
    solver.add(honda_civic_house >= 1, honda_civic_house <= 6)
    solver.add(Or([And(car_vars[i] == car_to_idx['honda civic'], honda_civic_house == i+1) for i in range(6)]))
    
    solver.add(Or(
        honda_civic_house == peter_house + 1,
        honda_civic_house == peter_house - 1
    ))
    
    # Clue 4: The person who is a lawyer is not in the fifth house.
    solver.add(occupation_vars[4] != occupation_to_idx['lawyer'])
    
    # Clue 5: The person who is a nurse is directly left of the person who is an artist.
    nurse_house = Int('nurse_house')
    solver.add(nurse_house >= 1, nurse_house <= 6)
    solver.add(Or([And(occupation_vars[i] == occupation_to_idx['nurse'], nurse_house == i+1) for i in range(6)]))
    
    artist_house = Int('artist_house')
    solver.add(artist_house >= 1, artist_house <= 6)
    solver.add(Or([And(occupation_vars[i] == occupation_to_idx['artist'], artist_house == i+1) for i in range(6)]))
    
    solver.add(artist_house == nurse_house + 1)
    
    # Clue 6: Carol is somewhere to the right of Eric.
    carol_house = Int('carol_house')
    solver.add(carol_house >= 1, carol_house <= 6)
    solver.add(Or([And(name_vars[i] == name_to_idx['Carol'], carol_house == i+1) for i in range(6)]))
    
    eric_house = Int('eric_house')
    solver.add(eric_house >= 1, eric_house <= 6)
    solver.add(Or([And(name_vars[i] == name_to_idx['Eric'], eric_house == i+1) for i in range(6)]))
    
    solver.add(carol_house > eric_house)
    
    # Clue 7: The person who is a doctor is Eric.
    solver.add(Or([And(name_vars[i] == name_to_idx['Eric'], occupation_vars[i] == occupation_to_idx['doctor']) for i in range(6)]))
    
    # Clue 8: The person who is a teacher is somewhere to the left of the person who is a nurse.
    teacher_house = Int('teacher_house')
    solver.add(teacher_house >= 1, teacher_house <= 6)
    solver.add(Or([And(occupation_vars[i] == occupation_to_idx['teacher'], teacher_house == i+1) for i in range(6)]))
    
    solver.add(teacher_house < nurse_house)
    
    # Clue 9: Carol is not in the sixth house.
    solver.add(name_vars[5] != name_to_idx['Carol'])
    
    # Clue 10: The person who is an engineer is Bob.
    solver.add(Or([And(name_vars[i] == name_to_idx['Bob'], occupation_vars[i] == occupation_to_idx['engineer']) for i in range(6)]))
    
    # Clue 11: The person who owns a Toyota Camry is the person who is a nurse.
    solver.add(Or([And(occupation_vars[i] == occupation_to_idx['nurse'], car_vars[i] == car_to_idx['toyota camry']) for i in range(6)]))
    
    # Clue 12: There is one house between Peter and the person who is a lawyer.
    lawyer_house = Int('lawyer_house')
    solver.add(lawyer_house >= 1, lawyer_house <= 6)
    solver.add(Or([And(occupation_vars[i] == occupation_to_idx['lawyer'], lawyer_house == i+1) for i in range(6)]))
    
    solver.add(Or(
        lawyer_house == peter_house + 2,
        lawyer_house == peter_house - 2
    ))
    
    # Clue 13: There is one house between the person who owns a Tesla Model 3 and Bob.
    tesla_house = Int('tesla_house')
    solver.add(tesla_house >= 1, tesla_house <= 6)
    solver.add(Or([And(car_vars[i] == car_to_idx['tesla model 3'], tesla_house == i+1) for i in range(6)]))
    
    bob_house = Int('bob_house')
    solver.add(bob_house >= 1, bob_house <= 6)
    solver.add(Or([And(name_vars[i] == name_to_idx['Bob'], bob_house == i+1) for i in range(6)]))
    
    solver.add(Or(
        tesla_house == bob_house + 2,
        tesla_house == bob_house - 2
    ))
    
    # Clue 14: Arnold is the person who is an artist.
    solver.add(Or([And(name_vars[i] == name_to_idx['Arnold'], occupation_vars[i] == occupation_to_idx['artist']) for i in range(6)]))
    
    # Check for solution
    if solver.check() == sat:
        model = solver.model()
        
        # Extract solution
        solution = []
        for i in range(n_houses):
            name_idx = model.evaluate(name_vars[i]).as_long()
            occupation_idx = model.evaluate(occupation_vars[i]).as_long()
            car_idx = model.evaluate(car_vars[i]).as_long()
            
            solution.append([
                str(i + 1),
                names[name_idx],
                occupations[occupation_idx],
                car_models[car_idx]
            ])
        
        # Format output as JSON
        output = {
            "solution": {
                "header": ["House", "Name", "Occupation", "CarModel"],
                "rows": solution
            }
        }
        
        print(json.dumps(output, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()