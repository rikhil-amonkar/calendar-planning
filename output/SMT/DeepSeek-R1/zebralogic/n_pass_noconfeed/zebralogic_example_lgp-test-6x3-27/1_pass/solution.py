import json
from z3 import *

def main():
    # Define the sorts for attributes
    Name = Datatype('Name')
    for n in ['Alice', 'Arnold', 'Eric', 'Peter', 'Bob', 'Carol']:
        Name.declare(n)
    Name = Name.create()
    
    Occupation = Datatype('Occupation')
    for o in ['engineer', 'artist', 'doctor', 'teacher', 'nurse', 'lawyer']:
        Occupation.declare(o)
    Occupation = Occupation.create()
    
    CarModel = Datatype('CarModel')
    for c in ['chevrolet_silverado', 'ford_f150', 'honda_civic', 'toyota_camry', 'bmw_3_series', 'tesla_model_3']:
        CarModel.declare(c)
    CarModel = CarModel.create()
    
    # Create solver and variables
    s = Solver()
    houses = [1, 2, 3, 4, 5, 6]
    names = [Const(f"name_{i}", Name) for i in houses]
    occupations = [Const(f"occ_{i}", Occupation) for i in houses]
    cars = [Const(f"car_{i}", CarModel) for i in houses]
    
    # All attributes are distinct
    s.add(Distinct(names))
    s.add(Distinct(occupations))
    s.add(Distinct(cars))
    
    # Add constraints from clues
    # 1. Ford F-150 in fifth house
    s.add(cars[4] == CarModel.ford_f150)
    
    # 2. Chevrolet Silverado not in second house
    s.add(cars[1] != CarModel.chevrolet_silverado)
    
    # 3. Honda Civic and Peter are adjacent
    peter_house = Int('peter_house')
    s.add(Or([And(names[i] == Name.Peter, Or(
        cars[i-1] == CarModel.honda_civic if i > 1 else False,
        cars[i+1] == CarModel.honda_civic if i < 5 else False
    )) for i in range(6)]))
    
    # 4. Lawyer not in fifth house
    s.add(occupations[4] != Occupation.lawyer)
    
    # 5. Nurse directly left of artist
    s.add(Or([And(occupations[i] == Occupation.nurse, occupations[i+1] == Occupation.artist) for i in range(5)]))
    
    # 6. Carol right of Eric
    eric_house = Int('eric_house')
    carol_house = Int('carol_house')
    s.add(eric_house < carol_house)
    for i in range(6):
        s.add(If(names[i] == Name.Eric, eric_house == i+1, True))
        s.add(If(names[i] == Name.Carol, carol_house == i+1, True))
    
    # 7. Doctor is Eric
    s.add(Or([And(names[i] == Name.Eric, occupations[i] == Occupation.doctor) for i in range(6)]))
    
    # 8. Teacher left of nurse
    teacher_house = Int('teacher_house')
    nurse_house = Int('nurse_house')
    s.add(teacher_house < nurse_house)
    for i in range(6):
        s.add(If(occupations[i] == Occupation.teacher, teacher_house == i+1, True))
        s.add(If(occupations[i] == Occupation.nurse, nurse_house == i+1, True))
    
    # 9. Carol not in sixth house
    s.add(names[5] != Name.Carol)
    
    # 10. Engineer is Bob
    s.add(Or([And(names[i] == Name.Bob, occupations[i] == Occupation.engineer) for i in range(6)]))
    
    # 11. Toyota Camry is nurse
    s.add(Or([And(occupations[i] == Occupation.nurse, cars[i] == CarModel.toyota_camry) for i in range(6)]))
    
    # 12. One house between Peter and lawyer
    peter_house = Int('peter_house2')
    lawyer_house = Int('lawyer_house')
    s.add(Or(Abs(peter_house - lawyer_house) == 2))
    for i in range(6):
        s.add(If(names[i] == Name.Peter, peter_house == i+1, True))
        s.add(If(occupations[i] == Occupation.lawyer, lawyer_house == i+1, True))
    
    # 13. One house between Tesla Model 3 and Bob
    tesla_house = Int('tesla_house')
    bob_house = Int('bob_house')
    s.add(Or(Abs(tesla_house - bob_house) == 2))
    for i in range(6):
        s.add(If(cars[i] == CarModel.tesla_model_3, tesla_house == i+1, True))
        s.add(If(names[i] == Name.Bob, bob_house == i+1, True))
    
    # 14. Arnold is artist
    s.add(Or([And(names[i] == Name.Arnold, occupations[i] == Occupation.artist) for i in range(6)]))
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        result = []
        for i in range(6):
            name_val = m.eval(names[i])
            occ_val = m.eval(occupations[i])
            car_val = m.eval(cars[i])
            
            # Convert to string representation
            name_str = str(name_val).split('!')[0].strip()
            occ_str = str(occ_val).split('!')[0].strip()
            car_str = str(car_val).split('!')[0].strip().replace('_', ' ')
            
            result.append([str(i+1), name_str, occ_str, car_str])
        
        output = {
            "solution": {
                "header": ["House", "Name", "Occupation", "CarModel"],
                "rows": result
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()