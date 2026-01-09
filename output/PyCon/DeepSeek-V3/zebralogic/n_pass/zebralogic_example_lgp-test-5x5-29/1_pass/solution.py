import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables for each attribute
    names = ['Eric', 'Peter', 'Alice', 'Bob', 'Arnold']
    nationalities = ['norwegian', 'brit', 'swede', 'dane', 'german']
    vacations = ['cruise', 'mountain', 'camping', 'beach', 'city']
    educations = ['bachelor', 'master', 'associate', 'doctorate', 'high school']
    occupations = ['artist', 'doctor', 'engineer', 'teacher', 'lawyer']
    
    houses = [1, 2, 3, 4, 5]
    
    # Add variables for each attribute per house
    problem.addVariables(['name'] + names, houses)
    problem.addVariables(['nationality'] + nationalities, houses)
    problem.addVariables(['vacation'] + vacations, houses)
    problem.addVariables(['education'] + educations, houses)
    problem.addVariables(['occupation'] + occupations, houses)
    
    # All attributes must have different houses
    problem.addConstraint(AllDifferentConstraint(), names)
    problem.addConstraint(AllDifferentConstraint(), nationalities)
    problem.addConstraint(AllDifferentConstraint(), vacations)
    problem.addConstraint(AllDifferentConstraint(), educations)
    problem.addConstraint(AllDifferentConstraint(), occupations)
    
    # Clue 1: The person who likes going on cruises is the person who is a lawyer.
    problem.addConstraint(lambda cruise, lawyer: cruise == lawyer, ['cruise', 'lawyer'])
    
    # Clue 2: The person who loves beach vacations is directly left of Arnold.
    problem.addConstraint(lambda beach, arnold: beach == arnold - 1, ['beach', 'Arnold'])
    
    # Clue 3: The person with a doctorate is somewhere to the left of Bob.
    problem.addConstraint(lambda doctorate, bob: doctorate < bob, ['doctorate', 'Bob'])
    
    # Clue 4: The person with an associate's degree is the person who likes going on cruises.
    problem.addConstraint(lambda associate, cruise: associate == cruise, ['associate', 'cruise'])
    
    # Clue 5: Peter is not in the first house.
    problem.addConstraint(lambda peter: peter != 1, ['Peter'])
    
    # Clue 6: The person who is an artist is Peter.
    problem.addConstraint(lambda artist, peter: artist == peter, ['artist', 'Peter'])
    
    # Clue 7: The person who enjoys camping trips is the person with a master's degree.
    problem.addConstraint(lambda camping, master: camping == master, ['camping', 'master'])
    
    # Clue 8: The Dane is somewhere to the right of the person who is a doctor.
    problem.addConstraint(lambda dane, doctor: dane > doctor, ['dane', 'doctor'])
    
    # Clue 9: The person with an associate's degree is directly left of the person who is an engineer.
    problem.addConstraint(lambda associate, engineer: associate == engineer - 1, ['associate', 'engineer'])
    
    # Clue 10: The person who enjoys camping trips is the British person.
    problem.addConstraint(lambda camping, brit: camping == brit, ['camping', 'brit'])
    
    # Clue 11: The Norwegian and the person with a bachelor's degree are next to each other.
    problem.addConstraint(lambda norwegian, bachelor: abs(norwegian - bachelor) == 1, ['norwegian', 'bachelor'])
    
    # Clue 12: The person who is an artist is the Swedish person.
    problem.addConstraint(lambda artist, swede: artist == swede, ['artist', 'swede'])
    
    # Clue 13: Bob is not in the fourth house.
    problem.addConstraint(lambda bob: bob != 4, ['Bob'])
    
    # Clue 14: The person who enjoys camping trips is Eric.
    problem.addConstraint(lambda camping, eric: camping == eric, ['camping', 'Eric'])
    
    # Clue 15: Alice is the German.
    problem.addConstraint(lambda alice, german: alice == german, ['Alice', 'german'])
    
    # Clue 16: The person who loves beach vacations is somewhere to the left of the person who prefers city breaks.
    problem.addConstraint(lambda beach, city: beach < city, ['beach', 'city'])
    
    # Clue 17: The person who enjoys mountain retreats is in the fifth house.
    problem.addConstraint(lambda mountain: mountain == 5, ['mountain'])
    
    # Clue 18: The person who likes going on cruises is somewhere to the right of the person who loves beach vacations.
    problem.addConstraint(lambda cruise, beach: cruise > beach, ['cruise', 'beach'])
    
    # Clue 19: The person with a bachelor's degree is in the third house.
    problem.addConstraint(lambda bachelor: bachelor == 3, ['bachelor'])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    solution = solutions[0]
    
    # Create the result structure
    result = {
        "solution": {
            "header": ["House", "Name", "Nationality", "Vacation", "Education", "Occupation"],
            "rows": []
        }
    }
    
    # Build the rows for each house
    for house in range(1, 6):
        row = [str(house)]
        
        # Find name for this house
        for name in names:
            if solution[name] == house:
                row.append(name)
                break
        
        # Find nationality for this house
        for nationality in nationalities:
            if solution[nationality] == house:
                row.append(nationality)
                break
        
        # Find vacation for this house
        for vacation in vacations:
            if solution[vacation] == house:
                row.append(vacation)
                break
        
        # Find education for this house
        for education in educations:
            if solution[education] == house:
                row.append(education)
                break
        
        # Find occupation for this house
        for occupation in occupations:
            if solution[occupation] == house:
                row.append(occupation)
                break
        
        result["solution"]["rows"].append(row)
    
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))