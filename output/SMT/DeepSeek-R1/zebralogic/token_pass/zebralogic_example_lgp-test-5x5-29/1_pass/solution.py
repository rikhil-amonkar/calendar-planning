import json
from z3 import *

def main():
    # Create solver
    s = Solver()

    # Define the categories and their possible values
    names = ['Eric', 'Peter', 'Alice', 'Bob', 'Arnold']
    nationalities = ['norwegian', 'brit', 'swede', 'dane', 'german']
    vacations = ['cruise', 'mountain', 'camping', 'beach', 'city']
    educations = ['bachelor', 'master', 'associate', 'doctorate', 'high school']
    occupations = ['artist', 'doctor', 'engineer', 'teacher', 'lawyer']

    # Create enumeration sorts for each category
    Name = Datatype('Name')
    for n in names:
        Name.declare(n)
    Name = Name.create()

    Nationality = Datatype('Nationality')
    for nat in nationalities:
        Nationality.declare(nat)
    Nationality = Nationality.create()

    Vacation = Datatype('Vacation')
    for v in vacations:
        Vacation.declare(v)
    Vacation = Vacation.create()

    Education = Datatype('Education')
    for e in educations:
        Education.declare(e)
    Education = Education.create()

    Occupation = Datatype('Occupation')
    for o in occupations:
        Occupation.declare(o)
    Occupation = Occupation.create()

    # Create variables for each house and each category
    houses = [1, 2, 3, 4, 5]
    name_vars = [Const(f'name_{i}', Name) for i in houses]
    nationality_vars = [Const(f'nationality_{i}', Nationality) for i in houses]
    vacation_vars = [Const(f'vacation_{i}', Vacation) for i in houses]
    education_vars = [Const(f'education_{i}', Education) for i in houses]
    occupation_vars = [Const(f'occupation_{i}', Occupation) for i in houses]

    # Each category must have distinct values across houses
    s.add(Distinct(name_vars))
    s.add(Distinct(nationality_vars))
    s.add(Distinct(vacation_vars))
    s.add(Distinct(education_vars))
    s.add(Distinct(occupation_vars))

    # Helper functions to get attribute constants
    def get_name(n): return getattr(Name, n)
    def get_nationality(n): return getattr(Nationality, n)
    def get_vacation(v): return getattr(Vacation, v)
    def get_education(e): return getattr(Education, e)
    def get_occupation(o): return getattr(Occupation, o)

    # Add constraints from clues
    # Clue 1: The person who likes going on cruises is the person who is a lawyer.
    for i in houses:
        s.add(Implies(vacation_vars[i-1] == get_vacation('cruise'), occupation_vars[i-1] == get_occupation('lawyer')))

    # Clue 2: The person who loves beach vacations is directly left of Arnold.
    for i in range(2, 6):
        s.add(Implies(vacation_vars[i-1] == get_vacation('beach'), name_vars[i] == get_name('Arnold')))
    s.add(Not(vacation_vars[4] == get_vacation('beach')))  # Arnold can't be in house 1

    # Clue 3: The person with a doctorate is somewhere to the left of Bob.
    for i in houses:
        for j in houses:
            if i >= j:
                continue
            s.add(Implies(education_vars[i-1] == get_education('doctorate'), name_vars[j-1] != get_name('Bob')))
        s.add(Implies(education_vars[i-1] == get_education('doctorate'), name_vars[i-1] != get_name('Bob')))

    # Clue 4: The person with an associate's degree is the person who likes going on cruises.
    for i in houses:
        s.add((education_vars[i-1] == get_education('associate')) == (vacation_vars[i-1] == get_vacation('cruise')))

    # Clue 5: Peter is not in the first house.
    s.add(name_vars[0] != get_name('Peter'))

    # Clue 6: The person who is an artist is Peter.
    for i in houses:
        s.add((occupation_vars[i-1] == get_occupation('artist')) == (name_vars[i-1] == get_name('Peter')))

    # Clue 7: The person who enjoys camping trips is the person with a master's degree.
    for i in houses:
        s.add((vacation_vars[i-1] == get_vacation('camping')) == (education_vars[i-1] == get_education('master')))

    # Clue 8: The Dane is somewhere to the right of the person who is a doctor.
    for i in houses:
        for j in range(i, 6):
            s.add(Implies(nationality_vars[j-1] == get_nationality('dane'), occupation_vars[i-1] != get_occupation('doctor')))
        s.add(Implies(nationality_vars[i-1] == get_nationality('dane'), occupation_vars[i-1] != get_occupation('doctor')))

    # Clue 9: The person with an associate's degree is directly left of the person who is an engineer.
    for i in range(1, 5):
        s.add(Implies(education_vars[i-1] == get_education('associate'), occupation_vars[i] == get_occupation('engineer')))
    s.add(Not(education_vars[4] == get_education('associate')))  # associate can't be in house 5

    # Clue 10: The person who enjoys camping trips is the British person.
    for i in houses:
        s.add((vacation_vars[i-1] == get_vacation('camping')) == (nationality_vars[i-1] == get_nationality('brit')))

    # Clue 11: The Norwegian and the person with a bachelor's degree are next to each other.
    for i in houses:
        for j in houses:
            if abs(i - j) != 1:
                s.add(Not(And(
                    nationality_vars[i-1] == get_nationality('norwegian'),
                    education_vars[j-1] == get_education('bachelor')
                )))

    # Clue 12: The person who is an artist is the Swedish person.
    for i in houses:
        s.add((occupation_vars[i-1] == get_occupation('artist')) == (nationality_vars[i-1] == get_nationality('swede')))

    # Clue 13: Bob is not in the fourth house.
    s.add(name_vars[3] != get_name('Bob'))

    # Clue 14: The person who enjoys camping trips is Eric.
    for i in houses:
        s.add((vacation_vars[i-1] == get_vacation('camping')) == (name_vars[i-1] == get_name('Eric')))

    # Clue 15: Alice is the German.
    for i in houses:
        s.add((name_vars[i-1] == get_name('Alice')) == (nationality_vars[i-1] == get_nationality('german')))

    # Clue 16: The person who loves beach vacations is somewhere to the left of the person who prefers city breaks.
    for i in houses:
        for j in houses:
            if i >= j:
                continue
            s.add(Implies(
                vacation_vars[i-1] == get_vacation('beach'),
                vacation_vars[j-1] != get_vacation('city')
            ))
        s.add(Implies(
            vacation_vars[i-1] == get_vacation('beach'),
            vacation_vars[i-1] != get_vacation('city')
        ))

    # Clue 17: The person who enjoys mountain retreats is in the fifth house.
    s.add(vacation_vars[4] == get_vacation('mountain'))

    # Clue 18: The person who likes going on cruises is somewhere to the right of the person who loves beach vacations.
    for i in houses:
        for j in houses:
            if i <= j:
                continue
            s.add(Implies(
                vacation_vars[i-1] == get_vacation('cruise'),
                vacation_vars[j-1] != get_vacation('beach')
            ))
        s.add(Implies(
            vacation_vars[i-1] == get_vacation('cruise'),
            vacation_vars[i-1] != get_vacation('beach')
        ))

    # Clue 19: The person with a bachelor's degree is in the third house.
    s.add(education_vars[2] == get_education('bachelor'))

    # Check and get the model
    if s.check() == sat:
        m = s.model()
        
        # Prepare the result table
        result = []
        for i in range(5):
            house_num = str(i+1)
            name_val = str(m.eval(name_vars[i]))
            nationality_val = str(m.eval(nationality_vars[i]))
            vacation_val = str(m.eval(vacation_vars[i]))
            education_val = str(m.eval(education_vars[i]))
            occupation_val = str(m.eval(occupation_vars[i]))
            result.append([house_num, name_val, nationality_val, vacation_val, education_val, occupation_val])
        
        # Create the output dictionary
        output = {
            "solution": {
                "header": ["House", "Name", "Nationality", "Vacation", "Education", "Occupation"],
                "rows": result
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()