from z3 import *
import json

def main():
    solver = Solver()
    
    # Define enums for each category
    Name = EnumSort('Name', ['Arnold', 'Bob', 'Peter', 'Alice', 'Carol', 'Eric'])
    Arnold, Bob, Peter, Alice, Carol, Eric = Name.consts()
    
    Food = EnumSort('Food', ['stew', 'grilled_cheese', 'stir_fry', 'soup', 'pizza', 'spaghetti'])
    stew, grilled_cheese, stir_fry, soup, pizza, spaghetti = Food.consts()
    
    Height = EnumSort('Height', ['tall', 'average', 'super_tall', 'very_short', 'very_tall', 'short'])
    tall, average, super_tall, very_short, very_tall, short = Height.consts()
    
    Drink = EnumSort('Drink', ['root_beer', 'boba_tea', 'coffee', 'water', 'tea', 'milk'])
    root_beer, boba_tea, coffee, water, tea, milk = Drink.consts()
    
    Pet = EnumSort('Pet', ['hamster', 'fish', 'cat', 'dog', 'bird', 'rabbit'])
    hamster, fish, cat, dog, bird, rabbit = Pet.consts()
    
    PhoneModel = EnumSort('PhoneModel', ['samsung_galaxy_s21', 'xiaomi_mi_11', 'google_pixel_6', 'iphone_13', 'huawei_p50', 'oneplus_9'])
    samsung_galaxy_s21, xiaomi_mi_11, google_pixel_6, iphone_13, huawei_p50, oneplus_9 = PhoneModel.consts()
    
    # Create arrays for each attribute per house
    names = [Const(f'name_{i}', Name) for i in range(1, 7)]
    foods = [Const(f'food_{i}', Food) for i in range(1, 7)]
    heights = [Const(f'height_{i}', Height) for i in range(1, 7)]
    drinks = [Const(f'drink_{i}', Drink) for i in range(1, 7)]
    pets = [Const(f'pet_{i}', Pet) for i in range(1, 7)]
    phones = [Const(f'phone_{i}', PhoneModel) for i in range(1, 7)]
    
    # Assert all attributes are distinct
    solver.add(Distinct(names))
    solver.add(Distinct(foods))
    solver.add(Distinct(heights))
    solver.add(Distinct(drinks))
    solver.add(Distinct(pets))
    solver.add(Distinct(phones))
    
    # Add constraints from clues
    # Clue 1: iPhone 13 in third house
    solver.add(phones[2] == iphone_13)
    
    # Clue 2: Bob is tall
    for i in range(6):
        solver.add(Implies(names[i] == Bob, heights[i] == tall))
    
    # Clue 3: Soup in second house
    solver.add(foods[1] == soup)
    
    # Clue 4: Root beer left of Xiaomi Mi 11
    solver.add(Or([And(drinks[i] == root_beer, phones[i+1] == xiaomi_mi_11) for i in range(5)]))
    
    # Clue 5: Huawei P50 left of grilled cheese
    solver.add(Or([And(phones[i] == huawei_p50, foods[i+1] == grilled_cheese) for i in range(5)]))
    
    # Clue 6: Stir fry and milk same house
    for i in range(6):
        solver.add(Implies(foods[i] == stir_fry, drinks[i] == milk))
    
    # Clue 7: Grilled cheese and tall same house
    for i in range(6):
        solver.add(Implies(foods[i] == grilled_cheese, heights[i] == tall))
    
    # Clue 8: Xiaomi Mi 11 and coffee same house
    for i in range(6):
        solver.add(Implies(phones[i] == xiaomi_mi_11, drinks[i] == coffee))
    
    # Clue 9: OnePlus 9 is Arnold
    for i in range(6):
        solver.add(Implies(phones[i] == oneplus_9, names[i] == Arnold))
    
    # Clue 10: Rabbit not in fifth house
    solver.add(pets[4] != rabbit)
    
    # Clue 11: Hamster right of Google Pixel 6
    for i in range(6):
        solver.add(Implies(phones[i] == google_pixel_6, Or([pets[j] == hamster for j in range(i+1, 6)])))
    
    # Clue 12: Super tall and fish same house
    for i in range(6):
        solver.add(Implies(heights[i] == super_tall, pets[i] == fish))
    
    # Clue 13: Fish is Alice
    for i in range(6):
        solver.add(Implies(pets[i] == fish, names[i] == Alice))
    
    # Clue 14: Tea left of pizza
    solver.add(Or([And(drinks[i] == tea, foods[i+1] == pizza) for i in range(5)]))
    
    # Clue 15: Samsung Galaxy S21 is Carol
    for i in range(6):
        solver.add(Implies(phones[i] == samsung_galaxy_s21, names[i] == Carol))
    
    # Clue 16: Pizza and short same house
    for i in range(6):
        solver.add(Implies(foods[i] == pizza, heights[i] == short))
    
    # Clue 17: Arnold is very tall
    for i in range(6):
        solver.add(Implies(names[i] == Arnold, heights[i] == very_tall))
    
    # Clue 18: Spaghetti and Google Pixel 6 same house
    for i in range(6):
        solver.add(Implies(foods[i] == spaghetti, phones[i] == google_pixel_6))
    
    # Clue 19: Boba tea right of soup
    for i in range(6):
        solver.add(Implies(foods[i] == soup, Or([drinks[j] == boba_tea for j in range(i+1, 6)])))
    
    # Clue 20: Hamster not in fifth house
    solver.add(pets[4] != hamster)
    
    # Clue 21: Very tall not in second house
    solver.add(heights[1] != very_tall)
    
    # Clue 22: Super tall left of Peter
    for i in range(6):
        solver.add(Implies(heights[i] == super_tall, Or([names[j] == Peter for j in range(i+1, 6)])))
    
    # Clue 23: Very short and spaghetti same house
    for i in range(6):
        solver.add(Implies(heights[i] == very_short, foods[i] == spaghetti))
    
    # Clue 24: Bird left of spaghetti
    for i in range(6):
        solver.add(Implies(pets[i] == bird, Or([foods[j] == spaghetti for j in range(i+1, 6)])))
    
    # Clue 25: Fish left of Eric
    solver.add(Or([And(pets[i] == fish, names[i+1] == Eric) for i in range(5)]))
    
    # Clue 26: Dog and milk same house
    for i in range(6):
        solver.add(Implies(pets[i] == dog, drinks[i] == milk))
    
    # Check solution
    if solver.check() == sat:
        model = solver.model()
        
        # Mapping from Z3 constants to original strings
        categories = [
            ('Name', Name, ['Arnold', 'Bob', 'Peter', 'Alice', 'Carol', 'Eric']),
            ('Food', Food, ['stew', 'grilled cheese', 'stir fry', 'soup', 'pizza', 'spaghetti']),
            ('Height', Height, ['tall', 'average', 'super tall', 'very short', 'very tall', 'short']),
            ('Drink', Drink, ['root beer', 'boba tea', 'coffee', 'water', 'tea', 'milk']),
            ('Pet', Pet, ['hamster', 'fish', 'cat', 'dog', 'bird', 'rabbit']),
            ('PhoneModel', PhoneModel, ['samsung galaxy s21', 'xiaomi mi 11', 'google pixel 6', 'iphone 13', 'huawei p50', 'oneplus 9'])
        ]
        
        output_map = {}
        for cat_name, enum_type, orig_list in categories:
            consts = enum_type.consts()
            output_map[cat_name] = {const: orig for const, orig in zip(consts, orig_list)}
        
        # Build result rows
        rows = []
        for i in range(6):
            house_num = str(i+1)
            n_val = model.evaluate(names[i])
            f_val = model.evaluate(foods[i])
            h_val = model.evaluate(heights[i])
            d_val = model.evaluate(drinks[i])
            p_val = model.evaluate(pets[i])
            ph_val = model.evaluate(phones[i])
            
            row = [
                house_num,
                output_map['Name'][n_val],
                output_map['Food'][f_val],
                output_map['Height'][h_val],
                output_map['Drink'][d_val],
                output_map['Pet'][p_val],
                output_map['PhoneModel'][ph_val]
            ]
            rows.append(row)
        
        # Create JSON output
        solution = {
            "solution": {
                "header": ["House", "Name", "Food", "Height", "Drink", "Pet", "PhoneModel"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()