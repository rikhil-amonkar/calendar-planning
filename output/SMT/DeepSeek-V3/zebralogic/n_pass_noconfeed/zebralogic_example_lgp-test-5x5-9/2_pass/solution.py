from z3 import *
import json

def main():
    # Create solver
    s = Solver()
    
    # Define the attributes
    names = ['Bob', 'Arnold', 'Peter', 'Alice', 'Eric']
    drinks = ['milk', 'root beer', 'coffee', 'tea', 'water']
    colors = ['blue', 'green', 'white', 'yellow', 'red']
    flowers = ['daffodils', 'roses', 'lilies', 'tulips', 'carnations']
    hobbies = ['painting', 'cooking', 'photography', 'gardening', 'knitting']
    
    # Create variables for each attribute in each house
    name_vars = [Int(f'name_{i}') for i in range(1, 6)]
    drink_vars = [Int(f'drink_{i}') for i in range(1, 6)]
    color_vars = [Int(f'color_{i}') for i in range(1, 6)]
    flower_vars = [Int(f'flower_{i}') for i in range(1, 6)]
    hobby_vars = [Int(f'hobby_{i}') for i in range(1, 6)]
    
    # Map attribute values to integers
    name_map = {i: name for i, name in enumerate(names)}
    drink_map = {i: drink for i, drink in enumerate(drinks)}
    color_map = {i: color for i, color in enumerate(colors)}
    flower_map = {i: flower for i, flower in enumerate(flowers)}
    hobby_map = {i: hobby for i, hobby in enumerate(hobbies)}
    
    # Each attribute must be a valid value (0-4)
    for i in range(5):
        s.add(And(name_vars[i] >= 0, name_vars[i] < 5))
        s.add(And(drink_vars[i] >= 0, drink_vars[i] < 5))
        s.add(And(color_vars[i] >= 0, color_vars[i] < 5))
        s.add(And(flower_vars[i] >= 0, flower_vars[i] < 5))
        s.add(And(hobby_vars[i] >= 0, hobby_vars[i] < 5))
    
    # All attributes must be distinct within their category
    s.add(Distinct(name_vars))
    s.add(Distinct(drink_vars))
    s.add(Distinct(color_vars))
    s.add(Distinct(flower_vars))
    s.add(Distinct(hobby_vars))
    
    # Clue 1: Alice is not in the fourth house
    alice_idx = names.index('Alice')
    s.add(name_vars[3] != alice_idx)  # House 4 is index 3
    
    # Clue 2: The root beer lover is the person who enjoys gardening
    root_beer_idx = drinks.index('root beer')
    gardening_idx = hobbies.index('gardening')
    for i in range(5):
        s.add(Implies(drink_vars[i] == root_beer_idx, hobby_vars[i] == gardening_idx))
    
    # Clue 3: The person whose favorite color is green is the coffee drinker
    green_idx = colors.index('green')
    coffee_idx = drinks.index('coffee')
    for i in range(5):
        s.add(Implies(color_vars[i] == green_idx, drink_vars[i] == coffee_idx))
    
    # Clue 4: The person whose favorite color is green is the person who loves the bouquet of lilies
    lilies_idx = flowers.index('lilies')
    for i in range(5):
        s.add(Implies(color_vars[i] == green_idx, flower_vars[i] == lilies_idx))
    
    # Clue 5: The person who loves blue is somewhere to the right of the person who loves a bouquet of daffodils
    blue_idx = colors.index('blue')
    daffodils_idx = flowers.index('daffodils')
    # Create a constraint that daffodils is left of blue
    daffodils_positions = [If(flower_vars[i] == daffodils_idx, i, -1) for i in range(5)]
    blue_positions = [If(color_vars[i] == blue_idx, i, -1) for i in range(5)]
    s.add(Exists([i, j], And(i >= 0, j >= 0, i < j, 
                            flower_vars[i] == daffodils_idx, 
                            color_vars[j] == blue_idx)))
    
    # Clue 6: The person who loves cooking is the person who loves blue
    cooking_idx = hobbies.index('cooking')
    for i in range(5):
        s.add(Implies(hobby_vars[i] == cooking_idx, color_vars[i] == blue_idx))
    
    # Clue 7: Eric is directly left of the tea drinker
    eric_idx = names.index('Eric')
    tea_idx = drinks.index('tea')
    for i in range(4):
        s.add(Implies(name_vars[i] == eric_idx, drink_vars[i+1] == tea_idx))
    
    # Clue 8: The one who only drinks water is Peter
    water_idx = drinks.index('water')
    peter_idx = names.index('Peter')
    for i in range(5):
        s.add(Implies(drink_vars[i] == water_idx, name_vars[i] == peter_idx))
    
    # Clue 9: Arnold is the photography enthusiast
    arnold_idx = names.index('Arnold')
    photography_idx = hobbies.index('photography')
    for i in range(5):
        s.add(Implies(name_vars[i] == arnold_idx, hobby_vars[i] == photography_idx))
    
    # Clue 10: The person who loves white is the person who loves the rose bouquet
    white_idx = colors.index('white')
    roses_idx = flowers.index('roses')
    for i in range(5):
        s.add(Implies(color_vars[i] == white_idx, flower_vars[i] == roses_idx))
    
    # Clue 11: There is one house between the person who loves a carnations arrangement and the person whose favorite color is red
    carnations_idx = flowers.index('carnations')
    red_idx = colors.index('red')
    # Create a constraint that they are exactly 2 positions apart
    carnations_red_constraint = Or(
        And(flower_vars[0] == carnations_idx, color_vars[2] == red_idx),
        And(flower_vars[1] == carnations_idx, color_vars[3] == red_idx),
        And(flower_vars[2] == carnations_idx, color_vars[4] == red_idx),
        And(flower_vars[2] == carnations_idx, color_vars[0] == red_idx),
        And(flower_vars[3] == carnations_idx, color_vars[1] == red_idx),
        And(flower_vars[4] == carnations_idx, color_vars[2] == red_idx),
        And(color_vars[0] == red_idx, flower_vars[2] == carnations_idx),
        And(color_vars[1] == red_idx, flower_vars[3] == carnations_idx),
        And(color_vars[2] == red_idx, flower_vars[4] == carnations_idx),
        And(color_vars[2] == red_idx, flower_vars[0] == carnations_idx),
        And(color_vars[3] == red_idx, flower_vars[1] == carnations_idx),
        And(color_vars[4] == red_idx, flower_vars[2] == carnations_idx)
    )
    s.add(carnations_red_constraint)
    
    # Clue 12: The person who loves cooking is somewhere to the left of the person who paints as a hobby
    painting_idx = hobbies.index('painting')
    # Create a constraint that cooking is left of painting
    cooking_positions = [If(hobby_vars[i] == cooking_idx, i, -1) for i in range(5)]
    painting_positions = [If(hobby_vars[i] == painting_idx, i, -1) for i in range(5)]
    s.add(Exists([i, j], And(i >= 0, j >= 0, i < j, 
                            hobby_vars[i] == cooking_idx, 
                            hobby_vars[j] == painting_idx)))
    
    # Clue 13: The one who only drinks water is in the third house
    s.add(drink_vars[2] == water_idx)  # House 3 is index 2
    
    # Clue 14: The person who loves a carnations arrangement is the root beer lover
    for i in range(5):
        s.add(Implies(flower_vars[i] == carnations_idx, drink_vars[i] == root_beer_idx))
    
    # Clue 15: The person who loves white is in the second house
    s.add(color_vars[1] == white_idx)  # House 2 is index 1
    
    # Check if solution exists
    if s.check() == sat:
        model = s.model()
        
        # Extract the solution
        solution = []
        for i in range(5):
            house_num = str(i + 1)
            name_val = name_map[model.evaluate(name_vars[i]).as_long()]
            drink_val = drink_map[model.evaluate(drink_vars[i]).as_long()]
            color_val = color_map[model.evaluate(color_vars[i]).as_long()]
            flower_val = flower_map[model.evaluate(flower_vars[i]).as_long()]
            hobby_val = hobby_map[model.evaluate(hobby_vars[i]).as_long()]
            
            solution.append([house_num, name_val, drink_val, color_val, flower_val, hobby_val])
        
        # Format the output as JSON
        output = {
            "solution": {
                "header": ["House", "Name", "Drink", "Color", "Flower", "Hobby"],
                "rows": solution
            }
        }
        
        print(json.dumps(output, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()