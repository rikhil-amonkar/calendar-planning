import z3
import json

def main():
    # Create solver
    solver = z3.Solver()
    
    # Define the number of houses
    n = 5
    houses = list(range(1, n+1))
    
    # Define attributes
    names = ['Eric', 'Peter', 'Alice', 'Bob', 'Arnold']
    nationalities = ['norwegian', 'brit', 'swede', 'dane', 'german']
    vacations = ['cruise', 'mountain', 'camping', 'beach', 'city']
    educations = ['bachelor', 'master', 'associate', 'doctorate', 'high school']
    occupations = ['artist', 'doctor', 'engineer', 'teacher', 'lawyer']
    
    # Create variables for each attribute per house
    name_vars = [z3.Int(f"name_{i}") for i in houses]
    nationality_vars = [z3.Int(f"nationality_{i}") for i in houses]
    vacation_vars = [z3.Int(f"vacation_{i}") for i in houses]
    education_vars = [z3.Int(f"education_{i}") for i in houses]
    occupation_vars = [z3.Int(f"occupation_{i}") for i in houses]
    
    # Define domains for each variable type
    name_domain = list(range(len(names)))
    nationality_domain = list(range(len(nationalities)))
    vacation_domain = list(range(len(vacations)))
    education_domain = list(range(len(educations)))
    occupation_domain = list(range(len(occupations)))
    
    # Constraint: All attributes within each category must be distinct and within domain
    for vars, domain in [(name_vars, name_domain), (nationality_vars, nationality_domain),
                         (vacation_vars, vacation_domain), (education_vars, education_domain),
                         (occupation_vars, occupation_domain)]:
        solver.add(z3.Distinct(vars))
        for var in vars:
            solver.add(z3.And(var >= min(domain), var <= max(domain)))
    
    # Helper function to get index of a value in a list
    def idx(lst, val):
        return lst.index(val)
    
    # Helper function for "directly left of" constraint
    def directly_left_of(a, b):
        return z3.Or([z3.And(a == i, b == i+1) for i in range(1, n)])
    
    # Helper function for "somewhere to the left of" constraint
    def left_of(a, b):
        return z3.Or([z3.And(a == i, b == j) for i in range(1, n+1) for j in range(i+1, n+1)])
    
    # Helper function for "next to" constraint
    def next_to(a, b):
        return z3.Or([z3.And(a == i, b == i+1) for i in range(1, n)] + 
                     [z3.And(a == i+1, b == i) for i in range(1, n)])
    
    # Clue 1: The person who likes going on cruises is the person who is a lawyer.
    cruise_idx = idx(vacations, 'cruise')
    lawyer_idx = idx(occupations, 'lawyer')
    for i in houses:
        solver.add(z3.Implies(vacation_vars[i-1] == cruise_idx, occupation_vars[i-1] == lawyer_idx))
    
    # Clue 2: The person who loves beach vacations is directly left of Arnold.
    beach_idx = idx(vacations, 'beach')
    arnold_idx = idx(names, 'Arnold')
    solver.add(directly_left_of(
        z3.If(vacation_vars[0] == beach_idx, 1, 
              z3.If(vacation_vars[1] == beach_idx, 2,
                    z3.If(vacation_vars[2] == beach_idx, 3,
                          z3.If(vacation_vars[3] == beach_idx, 4, 5)))),
        z3.If(name_vars[0] == arnold_idx, 1,
              z3.If(name_vars[1] == arnold_idx, 2,
                    z3.If(name_vars[2] == arnold_idx, 3,
                          z3.If(name_vars[3] == arnold_idx, 4, 5))))
    ))
    
    # Clue 3: The person with a doctorate is somewhere to the left of Bob.
    doctorate_idx = idx(educations, 'doctorate')
    bob_idx = idx(names, 'Bob')
    solver.add(left_of(
        z3.If(education_vars[0] == doctorate_idx, 1,
              z3.If(education_vars[1] == doctorate_idx, 2,
                    z3.If(education_vars[2] == doctorate_idx, 3,
                          z3.If(education_vars[3] == doctorate_idx, 4, 5)))),
        z3.If(name_vars[0] == bob_idx, 1,
              z3.If(name_vars[1] == bob_idx, 2,
                    z3.If(name_vars[2] == bob_idx, 3,
                          z3.If(name_vars[3] == bob_idx, 4, 5))))
    ))
    
    # Clue 4: The person with an associate's degree is the person who likes going on cruises.
    associate_idx = idx(educations, 'associate')
    for i in houses:
        solver.add(z3.Implies(education_vars[i-1] == associate_idx, vacation_vars[i-1] == cruise_idx))
    
    # Clue 5: Peter is not in the first house.
    peter_idx = idx(names, 'Peter')
    solver.add(name_vars[0] != peter_idx)
    
    # Clue 6: The person who is an artist is Peter.
    artist_idx = idx(occupations, 'artist')
    for i in houses:
        solver.add(z3.Implies(occupation_vars[i-1] == artist_idx, name_vars[i-1] == peter_idx))
    
    # Clue 7: The person who enjoys camping trips is the person with a master's degree.
    camping_idx = idx(vacations, 'camping')
    master_idx = idx(educations, 'master')
    for i in houses:
        solver.add(z3.Implies(vacation_vars[i-1] == camping_idx, education_vars[i-1] == master_idx))
    
    # Clue 8: The Dane is somewhere to the right of the person who is a doctor.
    dane_idx = idx(nationalities, 'dane')
    doctor_idx = idx(occupations, 'doctor')
    solver.add(left_of(
        z3.If(occupation_vars[0] == doctor_idx, 1,
              z3.If(occupation_vars[1] == doctor_idx, 2,
                    z3.If(occupation_vars[2] == doctor_idx, 3,
                          z3.If(occupation_vars[3] == doctor_idx, 4, 5)))),
        z3.If(nationality_vars[0] == dane_idx, 1,
              z3.If(nationality_vars[1] == dane_idx, 2,
                    z3.If(nationality_vars[2] == dane_idx, 3,
                          z3.If(nationality_vars[3] == dane_idx, 4, 5))))
    ))
    
    # Clue 9: The person with an associate's degree is directly left of the person who is an engineer.
    engineer_idx = idx(occupations, 'engineer')
    solver.add(directly_left_of(
        z3.If(education_vars[0] == associate_idx, 1,
              z3.If(education_vars[1] == associate_idx, 2,
                    z3.If(education_vars[2] == associate_idx, 3,
                          z3.If(education_vars[3] == associate_idx, 4, 5)))),
        z3.If(occupation_vars[0] == engineer_idx, 1,
              z3.If(occupation_vars[1] == engineer_idx, 2,
                    z3.If(occupation_vars[2] == engineer_idx, 3,
                          z3.If(occupation_vars[3] == engineer_idx, 4, 5))))
    ))
    
    # Clue 10: The person who enjoys camping trips is the British person.
    brit_idx = idx(nationalities, 'brit')
    for i in houses:
        solver.add(z3.Implies(vacation_vars[i-1] == camping_idx, nationality_vars[i-1] == brit_idx))
    
    # Clue 11: The Norwegian and the person with a bachelor's degree are next to each other.
    norwegian_idx = idx(nationalities, 'norwegian')
    bachelor_idx = idx(educations, 'bachelor')
    solver.add(next_to(
        z3.If(nationality_vars[0] == norwegian_idx, 1,
              z3.If(nationality_vars[1] == norwegian_idx, 2,
                    z3.If(nationality_vars[2] == norwegian_idx, 3,
                          z3.If(nationality_vars[3] == norwegian_idx, 4, 5)))),
        z3.If(education_vars[0] == bachelor_idx, 1,
              z3.If(education_vars[1] == bachelor_idx, 2,
                    z3.If(education_vars[2] == bachelor_idx, 3,
                          z3.If(education_vars[3] == bachelor_idx, 4, 5))))
    ))
    
    # Clue 12: The person who is an artist is the Swedish person.
    swede_idx = idx(nationalities, 'swede')
    for i in houses:
        solver.add(z3.Implies(occupation_vars[i-1] == artist_idx, nationality_vars[i-1] == swede_idx))
    
    # Clue 13: Bob is not in the fourth house.
    solver.add(name_vars[3] != bob_idx)
    
    # Clue 14: The person who enjoys camping trips is Eric.
    eric_idx = idx(names, 'Eric')
    for i in houses:
        solver.add(z3.Implies(vacation_vars[i-1] == camping_idx, name_vars[i-1] == eric_idx))
    
    # Clue 15: Alice is the German.
    alice_idx = idx(names, 'Alice')
    german_idx = idx(nationalities, 'german')
    for i in houses:
        solver.add(z3.Implies(name_vars[i-1] == alice_idx, nationality_vars[i-1] == german_idx))
    
    # Clue 16: The person who loves beach vacations is somewhere to the left of the person who prefers city breaks.
    city_idx = idx(vacations, 'city')
    solver.add(left_of(
        z3.If(vacation_vars[0] == beach_idx, 1,
              z3.If(vacation_vars[1] == beach_idx, 2,
                    z3.If(vacation_vars[2] == beach_idx, 3,
                          z3.If(vacation_vars[3] == beach_idx, 4, 5)))),
        z3.If(vacation_vars[0] == city_idx, 1,
              z3.If(vacation_vars[1] == city_idx, 2,
                    z3.If(vacation_vars[2] == city_idx, 3,
                          z3.If(vacation_vars[3] == city_idx, 4, 5))))
    ))
    
    # Clue 17: The person who enjoys mountain retreats is in the fifth house.
    mountain_idx = idx(vacations, 'mountain')
    solver.add(vacation_vars[4] == mountain_idx)
    
    # Clue 18: The person who likes going on cruises is somewhere to the right of the person who loves beach vacations.
    solver.add(left_of(
        z3.If(vacation_vars[0] == beach_idx, 1,
              z3.If(vacation_vars[1] == beach_idx, 2,
                    z3.If(vacation_vars[2] == beach_idx, 3,
                          z3.If(vacation_vars[3] == beach_idx, 4, 5)))),
        z3.If(vacation_vars[0] == cruise_idx, 1,
              z3.If(vacation_vars[1] == cruise_idx, 2,
                    z3.If(vacation_vars[2] == cruise_idx, 3,
                          z3.If(vacation_vars[3] == cruise_idx, 4, 5))))
    ))
    
    # Clue 19: The person with a bachelor's degree is in the third house.
    solver.add(education_vars[2] == bachelor_idx)
    
    # Check if the constraints are satisfiable
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Extract the solution
        solution = []
        for i in range(n):
            house_num = str(i+1)
            name = names[model.evaluate(name_vars[i]).as_long()]
            nationality = nationalities[model.evaluate(nationality_vars[i]).as_long()]
            vacation = vacations[model.evaluate(vacation_vars[i]).as_long()]
            education = educations[model.evaluate(education_vars[i]).as_long()]
            occupation = occupations[model.evaluate(occupation_vars[i]).as_long()]
            
            solution.append([house_num, name, nationality, vacation, education, occupation])
        
        # Format the output as JSON
        output = {
            "solution": {
                "header": ["House", "Name", "Nationality", "Vacation", "Education", "Occupation"],
                "rows": solution
            }
        }
        
        print(json.dumps(output, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()