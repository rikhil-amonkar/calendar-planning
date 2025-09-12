import z3
import json

def main():
    solver = z3.Solver()
    
    n_houses = 6
    houses = list(range(1, n_houses+1))
    
    # Define all attributes
    names = ['Arnold', 'Bob', 'Peter', 'Alice', 'Carol', 'Eric']
    foods = ['stew', 'grilled cheese', 'stir fry', 'soup', 'pizza', 'spaghetti']
    heights = ['tall', 'average', 'super tall', 'very short', 'very tall', 'short']
    drinks = ['root beer', 'boba tea', 'coffee', 'water', 'tea', 'milk']
    pets = ['hamster', 'fish', 'cat', 'dog', 'bird', 'rabbit']
    phones = ['samsung galaxy s21', 'xiaomi mi 11', 'google pixel 6', 'iphone 13', 'huawei p50', 'oneplus 9']
    
    # Create Z3 variables for each attribute
    name_vars = [z3.Int(f'name_{h}') for h in houses]
    food_vars = [z3.Int(f'food_{h}') for h in houses]
    height_vars = [z3.Int(f'height_{h}') for h in houses]
    drink_vars = [z3.Int(f'drink_{h}') for h in houses]
    pet_vars = [z3.Int(f'pet_{h}') for h in houses]
    phone_vars = [z3.Int(f'phone_{h}') for h in houses]
    
    # Define domain constraints
    for h in houses:
        solver.add(z3.And(name_vars[h-1] >= 0, name_vars[h-1] < len(names)))
        solver.add(z3.And(food_vars[h-1] >= 0, food_vars[h-1] < len(foods)))
        solver.add(z3.And(height_vars[h-1] >= 0, height_vars[h-1] < len(heights)))
        solver.add(z3.And(drink_vars[h-1] >= 0, drink_vars[h-1] < len(drinks)))
        solver.add(z3.And(pet_vars[h-1] >= 0, pet_vars[h-1] < len(pets)))
        solver.add(z3.And(phone_vars[h-1] >= 0, phone_vars[h-1] < len(phones)))
    
    # All attributes are distinct per house
    solver.add(z3.Distinct(name_vars))
    solver.add(z3.Distinct(food_vars))
    solver.add(z3.Distinct(height_vars))
    solver.add(z3.Distinct(drink_vars))
    solver.add(z3.Distinct(pet_vars))
    solver.add(z3.Distinct(phone_vars))
    
    # Helper function to get index
    def idx(lst, item):
        return lst.index(item)
    
    # Clue 1: The person who uses an iPhone 13 is in the third house.
    solver.add(phone_vars[2] == idx(phones, 'iphone 13'))
    
    # Clue 2: Bob is the person who is tall.
    solver.add(z3.Or([z3.And(name_vars[h] == idx(names, 'Bob'), 
                         height_vars[h] == idx(heights, 'tall')) for h in range(n_houses)]))
    
    # Clue 3: The person who loves the soup is in the second house.
    solver.add(food_vars[1] == idx(foods, 'soup'))
    
    # Clue 4: The root beer lover is directly left of the person who uses a Xiaomi Mi 11.
    for h in range(1, n_houses):
        solver.add(z3.Implies(
            drink_vars[h-1] == idx(drinks, 'root beer'),
            phone_vars[h] == idx(phones, 'xiaomi mi 11')
        ))
    
    # Clue 5: The person who uses a Huawei P50 is directly left of the person who loves eating grilled cheese.
    for h in range(1, n_houses):
        solver.add(z3.Implies(
            phone_vars[h-1] == idx(phones, 'huawei p50'),
            food_vars[h] == idx(foods, 'grilled cheese')
        ))
    
    # Clue 6: The person who loves stir fry is the person who likes milk.
    for h in range(n_houses):
        solver.add(z3.Implies(
            food_vars[h] == idx(foods, 'stir fry'),
            drink_vars[h] == idx(drinks, 'milk')
        ))
        solver.add(z3.Implies(
            drink_vars[h] == idx(drinks, 'milk'),
            food_vars[h] == idx(foods, 'stir fry')
        ))
    
    # Clue 7: The person who loves eating grilled cheese is the person who is tall.
    for h in range(n_houses):
        solver.add(z3.Implies(
            food_vars[h] == idx(foods, 'grilled cheese'),
            height_vars[h] == idx(heights, 'tall')
        ))
        solver.add(z3.Implies(
            height_vars[h] == idx(heights, 'tall'),
            food_vars[h] == idx(foods, 'grilled cheese')
        ))
    
    # Clue 8: The person who uses a Xiaomi Mi 11 is the coffee drinker.
    for h in range(n_houses):
        solver.add(z3.Implies(
            phone_vars[h] == idx(phones, 'xiaomi mi 11'),
            drink_vars[h] == idx(drinks, 'coffee')
        ))
        solver.add(z3.Implies(
            drink_vars[h] == idx(drinks, 'coffee'),
            phone_vars[h] == idx(phones, 'xiaomi mi 11')
        ))
    
    # Clue 9: The person who uses a OnePlus 9 is Arnold.
    for h in range(n_houses):
        solver.add(z3.Implies(
            phone_vars[h] == idx(phones, 'oneplus 9'),
            name_vars[h] == idx(names, 'Arnold')
        ))
        solver.add(z3.Implies(
            name_vars[h] == idx(names, 'Arnold'),
            phone_vars[h] == idx(phones, 'oneplus 9')
        ))
    
    # Clue 10: The person who owns a rabbit is not in the fifth house.
    solver.add(pet_vars[4] != idx(pets, 'rabbit'))
    
    # Clue 11: The person with a pet hamster is somewhere to the right of the person who uses a Google Pixel 6.
    hamster_right_of_pixel = []
    for h_pixel in range(n_houses):
        for h_hamster in range(h_pixel + 1, n_houses):
            hamster_right_of_pixel.append(z3.And(
                phone_vars[h_pixel] == idx(phones, 'google pixel 6'),
                pet_vars[h_hamster] == idx(pets, 'hamster')
            ))
    solver.add(z3.Or(hamster_right_of_pixel))
    
    # Clue 12: The person who is super tall is the person with an aquarium of fish.
    for h in range(n_houses):
        solver.add(z3.Implies(
            height_vars[h] == idx(heights, 'super tall'),
            pet_vars[h] == idx(pets, 'fish')
        ))
        solver.add(z3.Implies(
            pet_vars[h] == idx(pets, 'fish'),
            height_vars[h] == idx(heights, 'super tall')
        ))
    
    # Clue 13: The person with an aquarium of fish is Alice.
    for h in range(n_houses):
        solver.add(z3.Implies(
            pet_vars[h] == idx(pets, 'fish'),
            name_vars[h] == idx(names, 'Alice')
        ))
        solver.add(z3.Implies(
            name_vars[h] == idx(names, 'Alice'),
            pet_vars[h] == idx(pets, 'fish')
        ))
    
    # Clue 14: The tea drinker is directly left of the person who is a pizza lover.
    for h in range(1, n_houses):
        solver.add(z3.Implies(
            drink_vars[h-1] == idx(drinks, 'tea'),
            food_vars[h] == idx(foods, 'pizza')
        ))
    
    # Clue 15: The person who uses a Samsung Galaxy S21 is Carol.
    for h in range(n_houses):
        solver.add(z3.Implies(
            phone_vars[h] == idx(phones, 'samsung galaxy s21'),
            name_vars[h] == idx(names, 'Carol')
        ))
        solver.add(z3.Implies(
            name_vars[h] == idx(names, 'Carol'),
            phone_vars[h] == idx(phones, 'samsung galaxy s21')
        ))
    
    # Clue 16: The person who is a pizza lover is the person who is short.
    for h in range(n_houses):
        solver.add(z3.Implies(
            food_vars[h] == idx(foods, 'pizza'),
            height_vars[h] == idx(heights, 'short')
        ))
        solver.add(z3.Implies(
            height_vars[h] == idx(heights, 'short'),
            food_vars[h] == idx(foods, 'pizza')
        ))
    
    # Clue 17: Arnold is the person who is very tall.
    for h in range(n_houses):
        solver.add(z3.Implies(
            name_vars[h] == idx(names, 'Arnold'),
            height_vars[h] == idx(heights, 'very tall')
        ))
        solver.add(z3.Implies(
            height_vars[h] == idx(heights, 'very tall'),
            name_vars[h] == idx(names, 'Arnold')
        ))
    
    # Clue 18: The person who loves the spaghetti eater is the person who uses a Google Pixel 6.
    for h in range(n_houses):
        solver.add(z3.Implies(
            food_vars[h] == idx(foods, 'spaghetti'),
            phone_vars[h] == idx(phones, 'google pixel 6')
        ))
        solver.add(z3.Implies(
            phone_vars[h] == idx(phones, 'google pixel 6'),
            food_vars[h] == idx(foods, 'spaghetti')
        ))
    
    # Clue 19: The boba tea drinker is somewhere to the right of the person who loves the soup.
    boba_right_of_soup = []
    for h_soup in range(n_houses):
        for h_boba in range(h_soup + 1, n_houses):
            boba_right_of_soup.append(z3.And(
                food_vars[h_soup] == idx(foods, 'soup'),
                drink_vars[h_boba] == idx(drinks, 'boba tea')
            ))
    solver.add(z3.Or(boba_right_of_soup))
    
    # Clue 20: The person with a pet hamster is not in the fifth house.
    solver.add(pet_vars[4] != idx(pets, 'hamster'))
    
    # Clue 21: The person who is very tall is not in the second house.
    solver.add(height_vars[1] != idx(heights, 'very tall'))
    
    # Clue 22: The person who is super tall is somewhere to the left of Peter.
    super_tall_left_of_peter = []
    for h_st in range(n_houses):
        for h_peter in range(h_st + 1, n_houses):
            super_tall_left_of_peter.append(z3.And(
                height_vars[h_st] == idx(heights, 'super tall'),
                name_vars[h_peter] == idx(names, 'Peter')
            ))
    solver.add(z3.Or(super_tall_left_of_peter))
    
    # Clue 23: The person who is very short is the person who loves the spaghetti eater.
    for h in range(n_houses):
        solver.add(z3.Implies(
            height_vars[h] == idx(heights, 'very short'),
            food_vars[h] == idx(foods, 'spaghetti')
        ))
        solver.add(z3.Implies(
            food_vars[h] == idx(foods, 'spaghetti'),
            height_vars[h] == idx(heights, 'very short')
        ))
    
    # Clue 24: The person who keeps a pet bird is somewhere to the left of the person who loves the spaghetti eater.
    bird_left_of_spaghetti = []
    for h_bird in range(n_houses):
        for h_spaghetti in range(h_bird + 1, n_houses):
            bird_left_of_spaghetti.append(z3.And(
                pet_vars[h_bird] == idx(pets, 'bird'),
                food_vars[h_spaghetti] == idx(foods, 'spaghetti')
            ))
    solver.add(z3.Or(bird_left_of_spaghetti))
    
    # Clue 25: The person with an aquarium of fish is directly left of Eric.
    for h in range(1, n_houses):
        solver.add(z3.Implies(
            pet_vars[h-1] == idx(pets, 'fish'),
            name_vars[h] == idx(names, 'Eric')
        ))
    
    # Clue 26: The person who owns a dog is the person who likes milk.
    for h in range(n_houses):
        solver.add(z3.Implies(
            pet_vars[h] == idx(pets, 'dog'),
            drink_vars[h] == idx(drinks, 'milk')
        ))
        solver.add(z3.Implies(
            drink_vars[h] == idx(drinks, 'milk'),
            pet_vars[h] == idx(pets, 'dog')
        ))
    
    # Solve the constraints
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Extract the solution
        solution = []
        for h in houses:
            name_idx = model.evaluate(name_vars[h-1]).as_long()
            food_idx = model.evaluate(food_vars[h-1]).as_long()
            height_idx = model.evaluate(height_vars[h-1]).as_long()
            drink_idx = model.evaluate(drink_vars[h-1]).as_long()
            pet_idx = model.evaluate(pet_vars[h-1]).as_long()
            phone_idx = model.evaluate(phone_vars[h-1]).as_long()
            
            row = [
                str(h),
                names[name_idx],
                foods[food_idx],
                heights[height_idx],
                drinks[drink_idx],
                pets[pet_idx],
                phones[phone_idx]
            ]
            solution.append(row)
        
        # Format output as JSON
        output = {
            "solution": {
                "header": ["House", "Name", "Food", "Height", "Drink", "Pet", "PhoneModel"],
                "rows": solution
            }
        }
        
        print(json.dumps(output, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()