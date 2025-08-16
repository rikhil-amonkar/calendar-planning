from z3 import *
import json

def main():
    # Define the domains
    names_domain = ['Alice', 'Arnold', 'Eric', 'Peter', 'Bob', 'Carol']
    occ_domain = ['engineer', 'artist', 'doctor', 'teacher', 'nurse', 'lawyer']
    car_domain = ['chevrolet silverado', 'ford f150', 'honda civic', 'toyota camry', 'bmw 3 series', 'tesla model 3']

    # Create enum sorts
    NameSort, name_consts = EnumSort('Name', names_domain)
    OccSort, occ_consts = EnumSort('Occupation', occ_domain)
    CarSort, car_consts = EnumSort('CarModel', car_domain)

    # Create variables for each house (6 houses, index 0 to 5 for houses 1 to 6)
    names = [Const('name_%d' % i, NameSort) for i in range(6)]
    occupations = [Const('occ_%d' % i, OccSort) for i in range(6)]
    cars = [Const('car_%d' % i, CarSort) for i in range(6)]

    s = Solver()

    # Distinct constraints
    s.add(Distinct(names))
    s.add(Distinct(occupations))
    s.add(Distinct(cars))

    # Clue 1: The person who owns a Ford F-150 is in the fifth house.
    s.add(cars[4] == car_consts[1])  # ford f150 is index 1

    # Clue 2: The person who owns a Chevrolet Silverado is not in the second house.
    s.add(cars[1] != car_consts[0])  # chevrolet silverado is index 0

    # Clue 3: The person who owns a Honda Civic and Peter are next to each other.
    honda = car_consts[2]  # honda civic index 2
    peter = name_consts[3]  # Peter index 3
    or_clauses = []
    for i in range(5):  # Check adjacent pairs: (i, i+1) for i from 0 to 4
        # Honda at i and Peter at i+1, or Peter at i and Honda at i+1
        or_clauses.append(And(cars[i] == honda, names[i+1] == peter))
        or_clauses.append(And(names[i] == peter, cars[i+1] == honda))
    s.add(Or(or_clauses))

    # Clue 4: The person who is a lawyer is not in the fifth house.
    lawyer = occ_consts[5]  # lawyer index 5
    s.add(occupations[4] != lawyer)

    # Clue 5: The person who is a nurse is directly left of the person who is an artist.
    nurse = occ_consts[4]  # nurse index 4
    artist = occ_consts[1]  # artist index 1
    or_clauses = []
    for i in range(5):  # i from 0 to 4: nurse at i, artist at i+1
        or_clauses.append(And(occupations[i] == nurse, occupations[i+1] == artist))
    s.add(Or(or_clauses))

    # Clue 6: Carol is somewhere to the right of Eric.
    eric = name_consts[2]  # Eric index 2
    carol = name_consts[5]  # Carol index 5
    # If Carol is in house i, then Eric must be in some house j < i
    for i in range(6):
        # If house i has Carol, then there must be a house j in [0, i-1] with Eric
        s.add(Implies(names[i] == carol, Or([names[j] == eric for j in range(i)])))

    # Clue 7: The person who is a doctor is Eric.
    doctor = occ_consts[2]  # doctor index 2
    s.add([Implies(names[i] == eric, occupations[i] == doctor) for i in range(6)])

    # Clue 8: The person who is a teacher is somewhere to the left of the person who is a nurse.
    teacher = occ_consts[3]  # teacher index 3
    # If nurse is in house i, then there must be a teacher in house j < i
    for i in range(6):
        s.add(Implies(occupations[i] == nurse, Or([occupations[j] == teacher for j in range(i)])))

    # Clue 9: Carol is not in the sixth house.
    s.add(names[5] != carol)

    # Clue 10: The person who is an engineer is Bob.
    engineer = occ_consts[0]  # engineer index 0
    bob = name_consts[4]  # Bob index 4
    s.add([Implies(names[i] == bob, occupations[i] == engineer) for i in range(6)])

    # Clue 11: The person who owns a Toyota Camry is the person who is a nurse.
    toyota = car_consts[3]  # toyota camry index 3
    for i in range(6):
        s.add((cars[i] == toyota) == (occupations[i] == nurse))

    # Clue 12: There is one house between Peter and the person who is a lawyer.
    # This means |house_Peter - house_lawyer| = 2
    # Using integer variables for positions
    peter_house = Int('peter_house')
    lawyer_house = Int('lawyer_house')
    s.add(And(peter_house >= 0, peter_house < 6))
    s.add(And(lawyer_house >= 0, lawyer_house < 6))
    # Define the positions: peter_house is the index where names[i] == peter, etc.
    s.add(Or([And(names[i] == peter, peter_house == i) for i in range(6)]))
    s.add(Or([And(occupations[i] == lawyer, lawyer_house == i) for i in range(6)]))
    s.add(Or(peter_house == lawyer_house + 2, peter_house == lawyer_house - 2))

    # Clue 13: There is one house between the person who owns a Tesla Model 3 and Bob.
    tesla = car_consts[5]  # tesla model 3 index 5
    # Similarly, |house_tesla - house_bob| = 2
    tesla_house = Int('tesla_house')
    bob_house = Int('bob_house')
    s.add(And(tesla_house >= 0, tesla_house < 6))
    s.add(And(bob_house >= 0, bob_house < 6))
    s.add(Or([And(cars[i] == tesla, tesla_house == i) for i in range(6)]))
    s.add(Or([And(names[i] == bob, bob_house == i) for i in range(6)]))
    s.add(Or(tesla_house == bob_house + 2, tesla_house == bob_house - 2))

    # Clue 14: Arnold is the person who is an artist.
    arnold = name_consts[1]  # Arnold index 1
    for i in range(6):
        s.add((names[i] == arnold) == (occupations[i] == artist))

    # Check and get the model
    if s.check() == sat:
        model = s.model()
        # Map Z3 constants back to strings
        rows = []
        for i in range(6):
            name_val = model.eval(names[i])
            occ_val = model.eval(occupations[i])
            car_val = model.eval(cars[i])
            # Find the string for name
            name_str = None
            for idx, c in enumerate(name_consts):
                if name_val.eq(c):
                    name_str = names_domain[idx]
                    break
            occ_str = None
            for idx, c in enumerate(occ_consts):
                if occ_val.eq(c):
                    occ_str = occ_domain[idx]
                    break
            car_str = None
            for idx, c in enumerate(car_consts):
                if car_val.eq(c):
                    car_str = car_domain[idx]
                    break
            rows.append([str(i+1), name_str, occ_str, car_str])
        
        # Build the solution dictionary
        solution = {
            "solution": {
                "header": ["House", "Name", "Occupation", "CarModel"],
                "rows": rows
            }
        }
        print(json.dumps(solution))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()