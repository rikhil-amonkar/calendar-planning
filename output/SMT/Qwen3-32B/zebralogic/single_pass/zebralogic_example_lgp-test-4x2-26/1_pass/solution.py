import z3
import json

# Initialize the Z3 solver
solver = z3.Solver()

# Define variables for each person's house
Eric_house = z3.Int('Eric_house')
Peter_house = z3.Int('Peter_house')
Arnold_house = z3.Int('Arnold_house')
Alice_house = z3.Int('Alice_house')

# Define a boolean variable for whether Arnold is the doctor
is_arnold_doctor = z3.Bool('is_arnold_doctor')

# Add constraints for house numbers to be between 1 and 4
solver.add(z3.And(1 <= Eric_house, Eric_house <= 4))
solver.add(z3.And(1 <= Peter_house, Peter_house <= 4))
solver.add(z3.And(1 <= Arnold_house, Arnold_house <= 4))
solver.add(z3.And(1 <= Alice_house, Alice_house <= 4))

# All houses must be distinct
solver.add(z3.Distinct(Eric_house, Peter_house, Arnold_house, Alice_house))

# Clue 1: Two houses between Eric and Peter => |Eric_house - Peter_house| == 3
solver.add(z3.Abs(Eric_house - Peter_house) == 3)

# Clue 3: Peter is not in the first house
solver.add(Peter_house != 1)

# Clue 4: One house between the doctor and Alice => |doctor_house - Alice_house| == 2
doctor_house = z3.If(is_arnold_doctor, Arnold_house, Eric_house)
solver.add(z3.Abs(doctor_house - Alice_house) == 2)

# Check if the constraints are satisfiable
if solver.check() == z3.sat:
    model = solver.model()
    
    # Extract house numbers for each person
    eh = model[Eric_house].as_long()
    ph = model[Peter_house].as_long()
    ah = model[Arnold_house].as_long()
    aliceh = model[Alice_house].as_long()
    is_ad = model.evaluate(is_arnold_doctor).as_bool()
    
    # Map each house to its occupant and occupation
    house_to_name = {}
    house_to_occ = {}
    
    house_to_name[eh] = 'Eric'
    house_to_name[ph] = 'Peter'
    house_to_name[ah] = 'Arnold'
    house_to_name[aliceh] = 'Alice'
    
    # Assign known occupations
    house_to_occ[aliceh] = 'artist'
    house_to_occ[ph] = 'teacher'
    
    # Assign occupations for Arnold and Eric based on is_arnold_doctor
    if is_ad:
        house_to_occ[ah] = 'doctor'
        house_to_occ[eh] = 'engineer'
    else:
        house_to_occ[ah] = 'engineer'
        house_to_occ[eh] = 'doctor'
    
    # Build the rows in order of house numbers
    rows = []
    for house in [1, 2, 3, 4]:
        name = house_to_name[house]
        occupation = house_to_occ[house]
        rows.append([str(house), name, occupation])
    
    # Format the solution as JSON
    solution = {
        "solution": {
            "header": ["House", "Name", "Occupation"],
            "rows": rows
        }
    }
    
    # Output the JSON
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")