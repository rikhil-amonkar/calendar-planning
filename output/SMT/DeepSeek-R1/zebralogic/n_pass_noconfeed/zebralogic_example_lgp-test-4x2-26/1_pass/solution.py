import json
from z3 import *

def main():
    # Define the sorts for names and occupations
    Name = Datatype('Name')
    Name.declare('Arnold')
    Name.declare('Eric')
    Name.declare('Peter')
    Name.declare('Alice')
    Name = Name.create()

    Occupation = Datatype('Occupation')
    Occupation.declare('doctor')
    Occupation.declare('engineer')
    Occupation.declare('artist')
    Occupation.declare('teacher')
    Occupation = Occupation.create()

    # Create variables for each house's name and occupation
    names = [Const(f'name_{i}', Name) for i in range(1,5)]
    occupations = [Const(f'occupation_{i}', Occupation) for i in range(1,5)]

    s = Solver()

    # All names and occupations are distinct
    s.add(Distinct(names))
    s.add(Distinct(occupations))

    # Clue 1: Two houses between Eric and Peter
    # |Eric_house - Peter_house| = 3
    eric_house = Int('eric_house')
    peter_house = Int('peter_house')
    s.add(And(eric_house >= 1, eric_house <= 4))
    s.add(And(peter_house >= 1, peter_house <= 4))
    for idx, name in enumerate(names, 1):
        s.add(If(name == Name.Eric, eric_house == idx, True))
        s.add(If(name == Name.Peter, peter_house == idx, True))
    s.add(Or(
        And(eric_house == 1, peter_house == 4),
        And(eric_house == 4, peter_house == 1)
    ))

    # Clue 2: Teacher is Peter
    for i in range(4):
        s.add(If(occupations[i] == Occupation.teacher, names[i] == Name.Peter, True))

    # Clue 3: Peter not in first house
    s.add(names[0] != Name.Peter)

    # Clue 4: One house between doctor and Alice
    doctor_house = Int('doctor_house')
    alice_house = Int('alice_house')
    s.add(And(doctor_house >= 1, doctor_house <= 4))
    s.add(And(alice_house >= 1, alice_house <= 4))
    for idx, occ in enumerate(occupations, 1):
        s.add(If(occ == Occupation.doctor, doctor_house == idx, True))
    for idx, name in enumerate(names, 1):
        s.add(If(name == Name.Alice, alice_house == idx, True))
    s.add(Or(
        And(doctor_house == 1, alice_house == 3),
        And(doctor_house == 3, alice_house == 1),
        And(doctor_house == 2, alice_house == 4),
        And(doctor_house == 4, alice_house == 2)
    ))

    # Clue 5: Artist is Alice
    for i in range(4):
        s.add(If(occupations[i] == Occupation.artist, names[i] == Name.Alice, True))

    # Check and get the model
    if s.check() == sat:
        m = s.model()
        result = []
        for i in range(1,5):
            name_val = m.eval(names[i-1])
            occ_val = m.eval(occupations[i-1])
            result.append([str(i), str(name_val), str(occ_val)])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Occupation"],
                "rows": result
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()