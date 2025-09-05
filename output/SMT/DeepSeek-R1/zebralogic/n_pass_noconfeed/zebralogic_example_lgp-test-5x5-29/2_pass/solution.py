import json
from z3 import *

def main():
    s = Solver()
    num_houses = 5
    houses = list(range(num_houses))

    # Define enums for each attribute
    Name = Datatype('Name')
    for n in ['Eric', 'Peter', 'Alice', 'Bob', 'Arnold']:
        Name.declare(n)
    Name = Name.create()

    Nationality = Datatype('Nationality')
    for nt in ['norwegian', 'brit', 'swede', 'dane', 'german']:
        Nationality.declare(nt)
    Nationality = Nationality.create()

    Vacation = Datatype('Vacation')
    for v in ['cruise', 'mountain', 'camping', 'beach', 'city']:
        Vacation.declare(v)
    Vacation = Vacation.create()

    Education = Datatype('Education')
    for e in ['bachelor', 'master', 'associate', 'doctorate', 'high_school']:
        Education.declare(e)
    Education = Education.create()

    Occupation = Datatype('Occupation')
    for o in ['artist', 'doctor', 'engineer', 'teacher', 'lawyer']:
        Occupation.declare(o)
    Occupation = Occupation.create()

    # Create variables for each house and each attribute
    names = [Const(f'name_{i}', Name) for i in houses]
    nationalities = [Const(f'nationality_{i}', Nationality) for i in houses]
    vacations = [Const(f'vacation_{i}', Vacation) for i in houses]
    educations = [Const(f'education_{i}', Education) for i in houses]
    occupations = [Const(f'occupation_{i}', Occupation) for i in houses]

    # Add constraint: all attributes are distinct
    s.add(Distinct(names))
    s.add(Distinct(nationalities))
    s.add(Distinct(vacations))
    s.add(Distinct(educations))
    s.add(Distinct(occupations))

    # Define house indices for specific attributes
    bob_house = Int('bob_house')
    s.add(bob_house >= 0, bob_house < num_houses)
    for i in houses:
        s.add(If(names[i] == Name.Bob, bob_house == i, True))

    doctorate_house = Int('doctorate_house')
    s.add(doctorate_house >= 0, doctorate_house < num_houses)
    for i in houses:
        s.add(If(educations[i] == Education.doctorate, doctorate_house == i, True))

    doctor_house = Int('doctor_house')
    s.add(doctor_house >= 0, doctor_house < num_houses)
    for i in houses:
        s.add(If(occupations[i] == Occupation.doctor, doctor_house == i, True))

    dane_house = Int('dane_house')
    s.add(dane_house >= 0, dane_house < num_houses)
    for i in houses:
        s.add(If(nationalities[i] == Nationality.dane, dane_house == i, True))

    beach_house = Int('beach_house')
    s.add(beach_house >= 0, beach_house < num_houses)
    for i in houses:
        s.add(If(vacations[i] == Vacation.beach, beach_house == i, True))

    city_house = Int('city_house')
    s.add(city_house >= 0, city_house < num_houses)
    for i in houses:
        s.add(If(vacations[i] == Vacation.city, city_house == i, True))

    cruise_house = Int('cruise_house')
    s.add(cruise_house >= 0, cruise_house < num_houses)
    for i in houses:
        s.add(If(vacations[i] == Vacation.cruise, cruise_house == i, True))

    arnold_house = Int('arnold_house')
    s.add(arnold_house >= 0, arnold_house < num_houses)
    for i in houses:
        s.add(If(names[i] == Name.Arnold, arnold_house == i, True))

    associate_house = Int('associate_house')
    s.add(associate_house >= 0, associate_house < num_houses)
    for i in houses:
        s.add(If(educations[i] == Education.associate, associate_house == i, True))

    engineer_house = Int('engineer_house')
    s.add(engineer_house >= 0, engineer_house < num_houses)
    for i in houses:
        s.add(If(occupations[i] == Occupation.engineer, engineer_house == i, True))

    # Clue 1: Cruise lover is a lawyer
    for i in houses:
        s.add(Implies(vacations[i] == Vacation.cruise, occupations[i] == Occupation.lawyer))

    # Clue 2: Beach vacation is directly left of Arnold
    s.add(beach_house + 1 == arnold_house)

    # Clue 3: Doctorate is left of Bob
    s.add(doctorate_house < bob_house)

    # Clue 4: Associate's degree is cruise lover
    for i in houses:
        s.add(Implies(educations[i] == Education.associate, vacations[i] == Vacation.cruise))

    # Clue 5: Peter not in first house
    s.add(names[0] != Name.Peter)

    # Clue 6: Artist is Peter
    for i in houses:
        s.add(Implies(occupations[i] == Occupation.artist, names[i] == Name.Peter))

    # Clue 7: Camping is master's degree
    for i in houses:
        s.add(Implies(vacations[i] == Vacation.camping, educations[i] == Education.master))

    # Clue 8: Dane is right of doctor
    s.add(dane_house > doctor_house)

    # Clue 9: Associate's degree directly left of engineer
    s.add(associate_house + 1 == engineer_house)

    # Clue 10: Camping is British
    for i in houses:
        s.add(Implies(vacations[i] == Vacation.camping, nationalities[i] == Nationality.brit))

    # Clue 11: Norwegian and bachelor are adjacent
    bachelor_index = 2  # From clue 19
    s.add(Or(
        nationalities[bachelor_index - 1] == Nationality.norwegian,
        nationalities[bachelor_index + 1] == Nationality.norwegian
    ))

    # Clue 12: Artist is Swedish
    for i in houses:
        s.add(Implies(occupations[i] == Occupation.artist, nationalities[i] == Nationality.swede))

    # Clue 13: Bob not in fourth house
    s.add(names[3] != Name.Bob)

    # Clue 14: Camping is Eric
    for i in houses:
        s.add(Implies(vacations[i] == Vacation.camping, names[i] == Name.Eric))

    # Clue 15: Alice is German
    for i in houses:
        s.add(Implies(names[i] == Name.Alice, nationalities[i] == Nationality.german))

    # Clue 16: Beach left of city
    s.add(beach_house < city_house)

    # Clue 17: Mountain in fifth house
    s.add(vacations[4] == Vacation.mountain)

    # Clue 18: Cruise right of beach
    s.add(cruise_house > beach_house)

    # Clue 19: Bachelor in third house
    s.add(educations[2] == Education.bachelor)

    if s.check() == sat:
        m = s.model()
        result = []
        attributes = [names, nationalities, vacations, educations, occupations]
        attr_names = ['Name', 'Nationality', 'Vacation', 'Education', 'Occupation']
        for i in houses:
            house_data = [str(i + 1)]
            for attr_list in attributes:
                value = m[attr_list[i]]
                value_str = str(value)
                if value_str == 'high_school':
                    value_str = 'high school'
                house_data.append(value_str)
            result.append(house_data)
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