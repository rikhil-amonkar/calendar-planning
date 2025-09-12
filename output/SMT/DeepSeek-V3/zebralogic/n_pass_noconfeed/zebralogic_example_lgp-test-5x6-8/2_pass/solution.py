from z3 import *
import json

def main():
    # Create solver
    solver = Solver()
    
    # Define the houses
    n = 5
    houses = list(range(n))  # Use 0-based indexing
    
    # Define attributes
    names = ['Eric', 'Peter', 'Arnold', 'Bob', 'Alice']
    styles = ['modern', 'craftsman', 'ranch', 'victorian', 'colonial']
    mothers = ['Penny', 'Kailyn', 'Holly', 'Janelle', 'Aniya']
    phones = ['oneplus 9', 'google pixel 6', 'huawei p50', 'iphone 13', 'samsung galaxy s21']
    drinks = ['coffee', 'water', 'root beer', 'tea', 'milk']
    animals = ['fish', 'dog', 'horse', 'bird', 'cat']
    
    # Create variables for each attribute per house
    name_vars = [Int(f'name_{i}') for i in range(n)]
    style_vars = [Int(f'style_{i}') for i in range(n)]
    mother_vars = [Int(f'mother_{i}') for i in range(n)]
    phone_vars = [Int(f'phone_{i}') for i in range(n)]
    drink_vars = [Int(f'drink_{i}') for i in range(n)]
    animal_vars = [Int(f'animal_{i}') for i in range(n)]
    
    # Map attribute values to integers
    name_map = {i: name for i, name in enumerate(names)}
    style_map = {i: style for i, style in enumerate(styles)}
    mother_map = {i: mother for i, mother in enumerate(mothers)}
    phone_map = {i: phone for i, phone in enumerate(phones)}
    drink_map = {i: drink for i, drink in enumerate(drinks)}
    animal_map = {i: animal for i, animal in enumerate(animals)}
    
    # Each attribute is a permutation of 0-4
    for attr_vars in [name_vars, style_vars, mother_vars, phone_vars, drink_vars, animal_vars]:
        solver.add(Distinct(attr_vars))
        for var in attr_vars:
            solver.add(var >= 0, var < n)
    
    # Clue 1: The person who uses a Google Pixel 6 is not in the first house.
    pixel6_idx = phones.index('google pixel 6')
    solver.add(phone_vars[0] != pixel6_idx)
    
    # Clue 2: The one who only drinks water is Alice.
    water_idx = drinks.index('water')
    alice_idx = names.index('Alice')
    solver.add(drink_vars[alice_idx] == water_idx)
    
    # Clue 3: The person living in a colonial-style house is somewhere to the right of the person who uses a Huawei P50.
    colonial_idx = styles.index('colonial')
    huawei_idx = phones.index('huawei p50')
    for i in range(n):
        for j in range(n):
            if j <= i:
                solver.add(Implies(style_vars[i] == colonial_idx, phone_vars[j] != huawei_idx))
    
    # Clue 4: The person who keeps horses is the person who uses a OnePlus 9.
    horse_idx = animals.index('horse')
    oneplus_idx = phones.index('oneplus 9')
    for i in range(n):
        solver.add(Implies(animal_vars[i] == horse_idx, phone_vars[i] == oneplus_idx))
    
    # Clue 5: The person in a ranch-style home is The person whose mother's name is Kailyn.
    ranch_idx = styles.index('ranch')
    kailyn_idx = mothers.index('Kailyn')
    for i in range(n):
        solver.add(Implies(style_vars[i] == ranch_idx, mother_vars[i] == kailyn_idx))
    
    # Clue 6: The root beer lover is the cat lover.
    rootbeer_idx = drinks.index('root beer')
    cat_idx = animals.index('cat')
    for i in range(n):
        solver.add(Implies(drink_vars[i] == rootbeer_idx, animal_vars[i] == cat_idx))
    
    # Clue 7: The person living in a colonial-style house is not in the fourth house.
    solver.add(style_vars[3] != colonial_idx)
    
    # Clue 8: The bird keeper is in the fourth house.
    bird_idx = animals.index('bird')
    solver.add(animal_vars[3] == bird_idx)
    
    # Clue 9: The tea drinker is Bob.
    tea_idx = drinks.index('tea')
    bob_idx = names.index('Bob')
    solver.add(drink_vars[bob_idx] == tea_idx)
    
    # Clue 10: The tea drinker is somewhere to the right of The person whose mother's name is Kailyn.
    for i in range(n):
        for j in range(n):
            if j <= i:
                solver.add(Implies(drink_vars[i] == tea_idx, mother_vars[j] != kailyn_idx))
    
    # Clue 11: The root beer lover is somewhere to the left of The person whose mother's name is Kailyn.
    for i in range(n):
        for j in range(n):
            if j >= i:
                solver.add(Implies(drink_vars[i] == rootbeer_idx, mother_vars[j] != kailyn_idx))
    
    # Clue 12: The person who keeps horses is the person in a modern-style house.
    modern_idx = styles.index('modern')
    for i in range(n):
        solver.add(Implies(animal_vars[i] == horse_idx, style_vars[i] == modern_idx))
    
    # Clue 13: The person who uses an iPhone 13 is the person who likes milk.
    iphone_idx = phones.index('iphone 13')
    milk_idx = drinks.index('milk')
    for i in range(n):
        solver.add(Implies(phone_vars[i] == iphone_idx, drink_vars[i] == milk_idx))
    
    # Clue 14: The dog owner is the person who likes milk.
    dog_idx = animals.index('dog')
    for i in range(n):
        solver.add(Implies(animal_vars[i] == dog_idx, drink_vars[i] == milk_idx))
    
    # Clue 15: The person who uses a Google Pixel 6 is the person in a Craftsman-style house.
    craftsman_idx = styles.index('craftsman')
    for i in range(n):
        solver.add(Implies(phone_vars[i] == pixel6_idx, style_vars[i] == craftsman_idx))
    
    # Clue 16: Eric is not in the second house.
    eric_idx = names.index('Eric')
    solver.add(name_vars[1] != eric_idx)
    
    # Clue 17: The tea drinker is in the fourth house.
    solver.add(drink_vars[3] == tea_idx)
    
    # Clue 18: The person who keeps horses is in the third house.
    solver.add(animal_vars[2] == horse_idx)
    
    # Clue 19: The person in a modern-style house is The person whose mother's name is Penny.
    penny_idx = mothers.index('Penny')
    for i in range(n):
        solver.add(Implies(style_vars[i] == modern_idx, mother_vars[i] == penny_idx))
    
    # Clue 20: The root beer lover is Peter.
    peter_idx = names.index('Peter')
    solver.add(drink_vars[peter_idx] == rootbeer_idx)
    
    # Clue 21: The person whose mother's name is Aniya is not in the fourth house.
    aniya_idx = mothers.index('Aniya')
    solver.add(mother_vars[3] != aniya_idx)
    
    # Clue 22: The person whose mother's name is Janelle is the one who only drinks water.
    janelle_idx = mothers.index('Janelle')
    for i in range(n):
        solver.add(Implies(mother_vars[i] == janelle_idx, drink_vars[i] == water_idx))
    
    # Check if solution exists
    if solver.check() == sat:
        model = solver.model()
        
        # Prepare result
        result = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "Mother", "PhoneModel", "Drink", "Animal"],
                "rows": []
            }
        }
        
        for i in range(n):
            house_num = str(i + 1)
            name_val = name_map[model.evaluate(name_vars[i]).as_long()]
            style_val = style_map[model.evaluate(style_vars[i]).as_long()]
            mother_val = mother_map[model.evaluate(mother_vars[i]).as_long()]
            phone_val = phone_map[model.evaluate(phone_vars[i]).as_long()]
            drink_val = drink_map[model.evaluate(drink_vars[i]).as_long()]
            animal_val = animal_map[model.evaluate(animal_vars[i]).as_long()]
            
            result["solution"]["rows"].append([
                house_num, name_val, style_val, mother_val, phone_val, drink_val, animal_val
            ])
        
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()