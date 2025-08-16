from z3 import *

def main():
    # Define the attribute values
    names_list = ['Eric', 'Bob', 'Peter', 'Alice', 'Arnold', 'Carol']
    carmodels_list = ['ford f150', 'honda civic', 'toyota camry', 'tesla model 3', 'chevrolet silverado', 'bmw 3 series']
    mothers_list = ['Sarah', 'Penny', 'Holly', 'Aniya', 'Kailyn', 'Janelle']
    hobbies_list = ['photography', 'cooking', 'knitting', 'gardening', 'woodworking', 'painting']
    
    # Create enum sorts and value dictionaries
    NameSort, name_consts = EnumSort('Name', names_list)
    name_dict = {name: name_consts[i] for i, name in enumerate(names_list)}
    
    CarModelSort, carmodel_consts = EnumSort('CarModel', carmodels_list)
    carmodel_dict = {model: carmodel_consts[i] for i, model in enumerate(carmodels_list)}
    
    MotherSort, mother_consts = EnumSort('Mother', mothers_list)
    mother_dict = {mother: mother_consts[i] for i, mother in enumerate(mothers_list)}
    
    HobbySort, hobby_consts = EnumSort('Hobby', hobbies_list)
    hobby_dict = {hobby: hobby_consts[i] for i, hobby in enumerate(hobbies_list)}
    
    # Reverse dictionaries for decoding
    reverse_name = {v: k for k, v in name_dict.items()}
    reverse_carmodel = {v: k for k, v in carmodel_dict.items()}
    reverse_mother = {v: k for k, v in mother_dict.items()}
    reverse_hobby = {v: k for k, v in hobby_dict.items()}
    
    # Create functions for attributes
    Name_f = Function('Name', IntSort(), NameSort)
    CarModel_f = Function('CarModel', IntSort(), CarModelSort)
    Mother_f = Function('Mother', IntSort(), MotherSort)
    Hobby_f = Function('Hobby', IntSort(), HobbySort)
    
    s = Solver()
    houses = [1, 2, 3, 4, 5, 6]
    
    # Distinctness constraints
    s.add(Distinct([Name_f(h) for h in houses]))
    s.add(Distinct([CarModel_f(h) for h in houses]))
    s.add(Distinct([Mother_f(h) for h in houses]))
    s.add(Distinct([Hobby_f(h) for h in houses]))
    
    # Clue 1: Toyota Camry in house 6
    s.add(CarModel_f(6) == carmodel_dict['toyota camry'])
    
    # Clue 2: Carol is photography
    s.add(Or([And(Name_f(i) == name_dict['Carol'], Hobby_f(i) == hobby_dict['photography']) for i in houses]))
    
    # Clue 3: Chevrolet Silverado owner has mother Aniya
    s.add(Or([And(CarModel_f(i) == carmodel_dict['chevrolet silverado'], Mother_f(i) == mother_dict['Aniya']) for i in houses]))
    
    # Clue 4: Chevrolet Silverado not in house 2
    s.add(CarModel_f(2) != carmodel_dict['chevrolet silverado'])
    
    # Clue 5: Ford F-150 owner has mother Sarah
    s.add(Or([And(CarModel_f(i) == carmodel_dict['ford f150'], Mother_f(i) == mother_dict['Sarah']) for i in houses]))
    
    # Clue 6: BMW 3 Series owner is Bob
    s.add(Or([And(CarModel_f(i) == carmodel_dict['bmw 3 series'], Name_f(i) == name_dict['Bob']) for i in houses]))
    
    # Clue 7: Mother Kailyn in house 6
    s.add(Mother_f(6) == mother_dict['Kailyn'])
    
    # Clue 8: Eric directly left of knitting
    s.add(Or([And(Name_f(i) == name_dict['Eric'], Hobby_f(i + 1) == hobby_dict['knitting']) for i in range(1, 6)]))
    
    # Clue 9: One house between Sarah and Toyota Camry -> Sarah at house 4
    s.add(Mother_f(4) == mother_dict['Sarah'])
    
    # Clue 10: Mother Penny right of knitting
    s.add(Or([And(Mother_f(i) == mother_dict['Penny'], Hobby_f(j) == hobby_dict['knitting'], i > j) for i in houses for j in houses]))
    
    # Clue 11: Mother Aniya right of Honda Civic
    s.add(Or([And(Mother_f(i) == mother_dict['Aniya'], CarModel_f(j) == carmodel_dict['honda civic'], i > j) for i in houses for j in houses]))
    
    # Clue 12: Alice right of Ford F-150
    s.add(Or([And(Name_f(i) == name_dict['Alice'], CarModel_f(j) == carmodel_dict['ford f150'], i > j) for i in houses for j in houses]))
    
    # Clue 13: Eric is gardening
    s.add(Or([And(Name_f(i) == name_dict['Eric'], Hobby_f(i) == hobby_dict['gardening']) for i in houses]))
    
    # Clue 14: Woodworking left of knitting
    s.add(Or([And(Hobby_f(i) == hobby_dict['woodworking'], Hobby_f(j) == hobby_dict['knitting'], i < j) for i in houses for j in houses]))
    
    # Clue 15: One house between Sarah and cooking -> cooking at house 2 or 6
    s.add(Or(Hobby_f(2) == hobby_dict['cooking'], Hobby_f(6) == hobby_dict['cooking']))
    
    # Clue 16: Honda Civic owner is Arnold
    s.add(Or([And(CarModel_f(i) == carmodel_dict['honda civic'], Name_f(i) == name_dict['Arnold']) for i in houses]))
    
    # Clue 17: Mother Holly directly left of knitting
    s.add(Or([And(Mother_f(i) == mother_dict['Holly'], Hobby_f(i + 1) == hobby_dict['knitting']) for i in range(1, 6)]))
    
    # Check and get the model
    if s.check() == sat:
        m = s.model()
        rows = []
        for i in houses:
            name_val = m.evaluate(Name_f(i))
            car_val = m.evaluate(CarModel_f(i))
            mother_val = m.evaluate(Mother_f(i))
            hobby_val = m.evaluate(Hobby_f(i))
            
            name_str = reverse_name[name_val]
            car_str = reverse_carmodel[car_val]
            mother_str = reverse_mother[mother_val]
            hobby_str = reverse_hobby[hobby_val]
            
            rows.append([str(i), name_str, car_str, mother_str, hobby_str])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "CarModel", "Mother", "Hobby"],
                "rows": rows
            }
        }
        import json
        print(json.dumps(solution))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()