from z3 import *

def main():
    # Define the enums for each attribute
    Name, (Eric, Peter, Arnold, Alice, Bob) = EnumSort('Name', ['Eric', 'Peter', 'Arnold', 'Alice', 'Bob'])
    Food, (stir_fry, spaghetti, stew, grilled_cheese, pizza) = EnumSort('Food', ['stir fry', 'spaghetti', 'stew', 'grilled cheese', 'pizza'])
    CarModel, (ford_f150, tesla_model_3, bmw_3_series, toyota_camry, honda_civic) = EnumSort('CarModel', ['ford f150', 'tesla model 3', 'bmw 3 series', 'toyota camry', 'honda civic'])
    PhoneModel, (iphone_13, google_pixel_6, samsung_galaxy_s21, oneplus_9, huawei_p50) = EnumSort('PhoneModel', ['iphone 13', 'google pixel 6', 'samsung galaxy s21', 'oneplus 9', 'huawei p50'])
    Occupation, (teacher, lawyer, doctor, artist, engineer) = EnumSort('Occupation', ['teacher', 'lawyer', 'doctor', 'artist', 'engineer'])
    Drink, (tea, milk, water, root_beer, coffee) = EnumSort('Drink', ['tea', 'milk', 'water', 'root beer', 'coffee'])
    
    # Create the mapping from Z3 constants to string names for output
    name_map = { Eric: 'Eric', Peter: 'Peter', Arnold: 'Arnold', Alice: 'Alice', Bob: 'Bob' }
    food_map = { stir_fry: 'stir fry', spaghetti: 'spaghetti', stew: 'stew', grilled_cheese: 'grilled cheese', pizza: 'pizza' }
    car_map = { ford_f150: 'ford f150', tesla_model_3: 'tesla model 3', bmw_3_series: 'bmw 3 series', 
               toyota_camry: 'toyota camry', honda_civic: 'honda civic' }
    phone_map = { iphone_13: 'iphone 13', google_pixel_6: 'google pixel 6', samsung_galaxy_s21: 'samsung galaxy s21', 
                oneplus_9: 'oneplus 9', huawei_p50: 'huawei p50' }
    occupation_map = { teacher: 'teacher', lawyer: 'lawyer', doctor: 'doctor', artist: 'artist', engineer: 'engineer' }
    drink_map = { tea: 'tea', milk: 'milk', water: 'water', root_beer: 'root beer', coffee: 'coffee' }
    
    # Create arrays for each attribute for the 5 houses (index0 to index4 for house1 to house5)
    names = [Const('name_%d' % i, Name) for i in range(5)]
    foods = [Const('food_%d' % i, Food) for i in range(5)]
    carModels = [Const('carModel_%d' % i, CarModel) for i in range(5)]
    phoneModels = [Const('phoneModel_%d' % i, PhoneModel) for i in range(5)]
    occupations = [Const('occupation_%d' % i, Occupation) for i in range(5)]
    drinks = [Const('drink_%d' % i, Drink) for i in range(5)]
    
    s = Solver()
    
    # Add distinct constraints for each attribute
    s.add(Distinct(names))
    s.add(Distinct(foods))
    s.add(Distinct(carModels))
    s.add(Distinct(phoneModels))
    s.add(Distinct(occupations))
    s.add(Distinct(drinks))
    
    # Clue 17: Eric is in the fourth house (index3)
    s.add(names[3] == Eric)
    
    # Clue 3: Alice uses Samsung Galaxy S21
    # Clue 4: Alice loves stir fry
    # Clue 14: Alice is an artist
    for i in range(5):
        s.add(Implies(names[i] == Alice, phoneModels[i] == samsung_galaxy_s21))
        s.add(Implies(names[i] == Alice, foods[i] == stir_fry))
        s.add(Implies(names[i] == Alice, occupations[i] == artist))
    
    # Clue 19: The person who loves grilled cheese is Peter
    for i in range(5):
        s.add(Implies(foods[i] == grilled_cheese, names[i] == Peter))
    
    # Clue 7: The doctor is Arnold (equivalence)
    for i in range(5):
        s.add((occupations[i] == doctor) == (names[i] == Arnold))
    
    # Clue 16: Arnold owns Toyota Camry (equivalence)
    for i in range(5):
        s.add((names[i] == Arnold) == (carModels[i] == toyota_camry))
    
    # Clue 1: Root beer lover is Honda Civic owner (equivalence)
    for i in range(5):
        s.add((drinks[i] == root_beer) == (carModels[i] == honda_civic))
    
    # Clue 2: Milk drinker directly left of grilled cheese eater
    s.add(Or([And(drinks[i] == milk, foods[i+1] == grilled_cheese) for i in range(0,4)]))
    
    # Clue 5: Tea drinker not in fifth house (index4)
    s.add(drinks[4] != tea)
    
    # Clue 6: BMW owner is left of tea drinker
    terms_clue6 = []
    for i in range(5):
        for j in range(5):
            if i < j:
                terms_clue6.append(And(carModels[i] == bmw_3_series, drinks[j] == tea))
    s.add(Or(terms_clue6))
    
    # Clue 8: iPhone 13 user is coffee drinker
    for i in range(5):
        s.add(Implies(phoneModels[i] == iphone_13, drinks[i] == coffee))
    
    # Clue 9: Engineer owns BMW 3 Series (equivalence)
    for i in range(5):
        s.add((occupations[i] == engineer) == (carModels[i] == bmw_3_series))
    
    # Clue 10: Stew eater uses iPhone 13
    for i in range(5):
        s.add(Implies(foods[i] == stew, phoneModels[i] == iphone_13))
    
    # Clue 11: Doctor directly left of OnePlus 9 user
    s.add(Or([And(occupations[i] == doctor, phoneModels[i+1] == oneplus_9) for i in range(0,4)]))
    
    # Clue 12: Honda Civic owner directly left of spaghetti eater
    s.add(Or([And(carModels[i] == honda_civic, foods[i+1] == spaghetti) for i in range(0,4)]))
    
    # Clue 13: Google Pixel 6 user is tea drinker
    for i in range(5):
        s.add(Implies(phoneModels[i] == google_pixel_6, drinks[i] == tea))
    
    # Clue 15: One house between Alice and Ford F150 owner
    terms_clue15 = []
    for i in range(5):
        j1 = i-2
        j2 = i+2
        if j1 >= 0 and j1 < 5:
            terms_clue15.append(And(names[i] == Alice, carModels[j1] == ford_f150))
        if j2 >= 0 and j2 < 5:
            terms_clue15.append(And(names[i] == Alice, carModels[j2] == ford_f150))
    s.add(Or(terms_clue15))
    
    # Clue 18: OnePlus 9 user is lawyer (equivalence)
    for i in range(5):
        s.add((phoneModels[i] == oneplus_9) == (occupations[i] == lawyer))
    
    # Check and get the model
    if s.check() == sat:
        m = s.model()
        rows = []
        for i in range(5):
            name_val = m.eval(names[i])
            food_val = m.eval(foods[i])
            car_val = m.eval(carModels[i])
            phone_val = m.eval(phoneModels[i])
            occ_val = m.eval(occupations[i])
            drink_val = m.eval(drinks[i])
            
            name_str = name_map[name_val]
            food_str = food_map[food_val]
            car_str = car_map[car_val]
            phone_str = phone_map[phone_val]
            occ_str = occupation_map[occ_val]
            drink_str = drink_map[drink_val]
            
            rows.append([str(i+1), name_str, food_str, car_str, phone_str, occ_str, drink_str])
        
        solution = {
            "solution": {
                "header": ["House", "Name", "Food", "CarModel", "PhoneModel", "Occupation", "Drink"],
                "rows": rows
            }
        }
        
        import json
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()