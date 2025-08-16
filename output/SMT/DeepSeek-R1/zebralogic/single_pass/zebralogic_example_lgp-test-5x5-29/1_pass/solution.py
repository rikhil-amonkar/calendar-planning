from z3 import *

def main():
    # Define the attributes
    names = ['Eric', 'Peter', 'Alice', 'Bob', 'Arnold']
    nationalities = ['norwegian', 'brit', 'swede', 'dane', 'german']
    vacations = ['cruise', 'mountain', 'camping', 'beach', 'city']
    educations = ['bachelor', 'master', 'associate', 'doctorate', 'high school']
    occupations = ['artist', 'doctor', 'engineer', 'teacher', 'lawyer']
    
    # Create enums for each attribute
    Name = EnumSort('Name', names)
    Nationality = EnumSort('Nationality', nationalities)
    Vacation = EnumSort('Vacation', vacations)
    Education = EnumSort('Education', educations)
    Occupation = EnumSort('Occupation', occupations)
    
    # Create variables for each house and attribute
    house_names = [Const(f'name_{i}', Name) for i in range(5)]
    house_nationalities = [Const(f'nationality_{i}', Nationality) for i in range(5)]
    house_vacations = [Const(f'vacation_{i}', Vacation) for i in range(5)]
    house_educations = [Const(f'education_{i}', Education) for i in range(5)]
    house_occupations = [Const(f'occupation_{i}', Occupation) for i in range(5)]
    
    s = Solver()
    
    # Add distinct constraints for each attribute
    s.add(Distinct(house_names))
    s.add(Distinct(house_nationalities))
    s.add(Distinct(house_vacations))
    s.add(Distinct(house_educations))
    s.add(Distinct(house_occupations))
    
    # Helper functions to get attribute values
    def get_name(i): return house_names[i]
    def get_nationality(i): return house_nationalities[i]
    def get_vacation(i): return house_vacations[i]
    def get_education(i): return house_educations[i]
    def get_occupation(i): return house_occupations[i]
    
    # Clue 1: Cruise lover is the lawyer
    for i in range(5):
        s.add(Implies(get_vacation(i) == Const('cruise', Vacation), 
                      get_occupation(i) == Const('lawyer', Occupation)))
    
    # Clue 2: Beach lover is directly left of Arnold
    for i in range(4):  # Houses 1-4 (0-3 index) can have someone left
        s.add(Implies(get_vacation(i) == Const('beach', Vacation),
                      get_name(i+1) == Const('Arnold', Name)))
    
    # Clue 3: Doctorate is left of Bob
    doctorate_index = Int('doctorate_index')
    bob_index = Int('bob_index')
    s.add(doctorate_index >= 0, doctorate_index < 5)
    s.add(bob_index >= 0, bob_index < 5)
    for i in range(5):
        s.add(If(get_education(i) == Const('doctorate', Education), doctorate_index == i, True))
        s.add(If(get_name(i) == Const('Bob', Name), bob_index == i, True))
    s.add(doctorate_index < bob_index)
    
    # Clue 4: Associate degree is cruise lover
    for i in range(5):
        s.add(Implies(get_education(i) == Const('associate', Education), 
                      get_vacation(i) == Const('cruise', Vacation)))
    
    # Clue 5: Peter not in first house
    s.add(get_name(0) != Const('Peter', Name))
    
    # Clue 6: Artist is Peter
    for i in range(5):
        s.add(Implies(get_occupation(i) == Const('artist', Occupation), 
                      get_name(i) == Const('Peter', Name)))
    
    # Clue 7: Camper has master's degree
    for i in range(5):
        s.add(Implies(get_vacation(i) == Const('camping', Vacation), 
                      get_education(i) == Const('master', Education)))
    
    # Clue 8: Dane is right of doctor
    dane_index = Int('dane_index')
    doctor_index = Int('doctor_index')
    s.add(dane_index >= 0, dane_index < 5)
    s.add(doctor_index >= 0, doctor_index < 5)
    for i in range(5):
        s.add(If(get_nationality(i) == Const('dane', Nationality), dane_index == i, True))
        s.add(If(get_occupation(i) == Const('doctor', Occupation), doctor_index == i, True))
    s.add(dane_index > doctor_index)
    
    # Clue 9: Associate degree directly left of engineer
    for i in range(4):
        s.add(Implies(get_education(i) == Const('associate', Education),
                      get_occupation(i+1) == Const('engineer', Occupation)))
    
    # Clue 10: Camper is British
    for i in range(5):
        s.add(Implies(get_vacation(i) == Const('camping', Vacation), 
                      get_nationality(i) == Const('brit', Nationality)))
    
    # Clue 11: Norwegian and bachelor's degree are adjacent
    norwegian_index = Int('norwegian_index')
    bachelor_index = Int('bachelor_index')
    s.add(norwegian_index >= 0, norwegian_index < 5)
    s.add(bachelor_index >= 0, bachelor_index < 5)
    for i in range(5):
        s.add(If(get_nationality(i) == Const('norwegian', Nationality), norwegian_index == i, True))
        s.add(If(get_education(i) == Const('bachelor', Education), bachelor_index == i, True))
    s.add(Or(norwegian_index == bachelor_index + 1, norwegian_index == bachelor_index - 1))
    
    # Clue 12: Artist is Swedish
    for i in range(5):
        s.add(Implies(get_occupation(i) == Const('artist', Occupation), 
                      get_nationality(i) == Const('swede', Nationality)))
    
    # Clue 13: Bob not in fourth house
    s.add(get_name(3) != Const('Bob', Name))
    
    # Clue 14: Camper is Eric
    for i in range(5):
        s.add(Implies(get_vacation(i) == Const('camping', Vacation), 
                      get_name(i) == Const('Eric', Name)))
    
    # Clue 15: Alice is German
    for i in range(5):
        s.add(Implies(get_name(i) == Const('Alice', Name), 
                      get_nationality(i) == Const('german', Nationality)))
    
    # Clue 16: Beach left of city
    beach_index = Int('beach_index')
    city_index = Int('city_index')
    s.add(beach_index >= 0, beach_index < 5)
    s.add(city_index >= 0, city_index < 5)
    for i in range(5):
        s.add(If(get_vacation(i) == Const('beach', Vacation), beach_index == i, True))
        s.add(If(get_vacation(i) == Const('city', Vacation), city_index == i, True))
    s.add(beach_index < city_index)
    
    # Clue 17: Mountain in fifth house
    s.add(get_vacation(4) == Const('mountain', Vacation))
    
    # Clue 18: Cruise right of beach
    cruise_index = Int('cruise_index')
    s.add(cruise_index >= 0, cruise_index < 5)
    for i in range(5):
        s.add(If(get_vacation(i) == Const('cruise', Vacation), cruise_index == i, True))
    s.add(cruise_index > beach_index)
    
    # Clue 19: Bachelor in third house
    s.add(get_education(2) == Const('bachelor', Education))
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        
        # Map back to string values
        name_map = {getattr(Name, name): name for name in names}
        nationality_map = {getattr(Nationality, nat): nat for nat in nationalities}
        vacation_map = {getattr(Vacation, vac): vac for vac in vacations}
        education_map = {getattr(Education, edu): edu for edu in educations}
        occupation_map = {getattr(Occupation, occ): occ for occ in occupations}
        
        rows = []
        for i in range(5):
            name_val = name_map[m.eval(house_names[i])]
            nat_val = nationality_map[m.eval(house_nationalities[i])]
            vac_val = vacation_map[m.eval(house_vacations[i])]
            edu_val = education_map[m.eval(house_educations[i])]
            occ_val = occupation_map[m.eval(house_occupations[i])]
            rows.append([str(i+1), name_val, nat_val, vac_val, edu_val, occ_val])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Nationality", "Vacation", "Education", "Occupation"],
                "rows": rows
            }
        }
        
        import json
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()