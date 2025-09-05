import z3
import json

def main():
    # Define the categories and their possible values
    categories = {
        'Name': ['Bob', 'Arnold', 'Peter', 'Alice', 'Eric'],
        'Drink': ['milk', 'root beer', 'coffee', 'tea', 'water'],
        'Color': ['blue', 'green', 'white', 'yellow', 'red'],
        'Flower': ['daffodils', 'roses', 'lilies', 'tulips', 'carnations'],
        'Hobby': ['painting', 'cooking', 'photography', 'gardening', 'knitting']
    }
    
    # Create EnumSorts for each category
    NameSort, (Bob, Arnold, Peter, Alice, Eric) = z3.EnumSort('Name', categories['Name'])
    DrinkSort, (milk, root_beer, coffee, tea, water) = z3.EnumSort('Drink', categories['Drink'])
    ColorSort, (blue, green, white, yellow, red) = z3.EnumSort('Color', categories['Color'])
    FlowerSort, (daffodils, roses, lilies, tulips, carnations) = z3.EnumSort('Flower', categories['Flower'])
    HobbySort, (painting, cooking, photography, gardening, knitting) = z3.EnumSort('Hobby', categories['Hobby'])
    
    # Create arrays for each attribute for 5 houses (index 0 to 4)
    names = [z3.Const(f'name_{i}', NameSort) for i in range(5)]
    drinks = [z3.Const(f'drink_{i}', DrinkSort) for i in range(5)]
    colors = [z3.Const(f'color_{i}', ColorSort) for i in range(5)]
    flowers = [z3.Const(f'flower_{i}', FlowerSort) for i in range(5)]
    hobbies = [z3.Const(f'hobby_{i}', HobbySort) for i in range(5)]
    
    solver = z3.Solver()
    
    # Each attribute must have distinct values across houses
    solver.add(z3.Distinct(names))
    solver.add(z3.Distinct(drinks))
    solver.add(z3.Distinct(colors))
    solver.add(z3.Distinct(flowers))
    solver.add(z3.Distinct(hobbies))
    
    # Clue 1: Alice is not in the fourth house (index 3)
    solver.add(names[3] != Alice)
    
    # Clue 2: The root beer lover is the person who enjoys gardening
    for i in range(5):
        solver.add(z3.Implies(drinks[i] == root_beer, hobbies[i] == gardening))
    
    # Clue 3: The person whose favorite color is green is the coffee drinker
    for i in range(5):
        solver.add(z3.Implies(colors[i] == green, drinks[i] == coffee))
    
    # Clue 4: The person whose favorite color is green is the person who loves the bouquet of lilies
    for i in range(5):
        solver.add(z3.Implies(colors[i] == green, flowers[i] == lilies))
    
    # Clue 5: The person who loves blue is to the right of the person who loves daffodils
    daffodils_house = z3.Int('daffodils_house')
    blue_house = z3.Int('blue_house')
    solver.add(z3.And([z3.Implies(flowers[i] == daffodils, daffodils_house == i) for i in range(5)]))
    solver.add(z3.And([z3.Implies(colors[i] == blue, blue_house == i) for i in range(5)]))
    solver.add(blue_house > daffodils_house)
    
    # Clue 6: The person who loves cooking is the person who loves blue
    for i in range(5):
        solver.add(z3.Implies(hobbies[i] == cooking, colors[i] == blue))
    
    # Clue 7: Eric is directly left of the tea drinker
    eric_house = z3.Int('eric_house')
    tea_house = z3.Int('tea_house')
    solver.add(z3.And([z3.Implies(names[i] == Eric, eric_house == i) for i in range(5)]))
    solver.add(z3.And([z3.Implies(drinks[i] == tea, tea_house == i) for i in range(5)]))
    solver.add(tea_house == eric_house + 1)
    
    # Clue 8: The one who only drinks water is Peter
    for i in range(5):
        solver.add(z3.Implies(drinks[i] == water, names[i] == Peter))
    
    # Clue 9: Arnold is the photography enthusiast
    for i in range(5):
        solver.add(z3.Implies(names[i] == Arnold, hobbies[i] == photography))
    
    # Clue 10: The person who loves white is the person who loves the rose bouquet
    for i in range(5):
        solver.add(z3.Implies(colors[i] == white, flowers[i] == roses))
    
    # Clue 11: One house between carnations and red color
    carnations_house = z3.Int('carnations_house')
    red_house = z3.Int('red_house')
    solver.add(z3.And([z3.Implies(flowers[i] == carnations, carnations_house == i) for i in range(5)]))
    solver.add(z3.And([z3.Implies(colors[i] == red, red_house == i) for i in range(5)]))
    solver.add(z3.Or(red_house - carnations_house == 2, carnations_house - red_house == 2))
    
    # Clue 12: Cooking is left of painting
    cooking_house = z3.Int('cooking_house')
    painting_house = z3.Int('painting_house')
    solver.add(z3.And([z3.Implies(hobbies[i] == cooking, cooking_house == i) for i in range(5)]))
    solver.add(z3.And([z3.Implies(hobbies[i] == painting, painting_house == i) for i in range(5)]))
    solver.add(cooking_house < painting_house)
    
    # Clue 13: Water drinker is in third house (index 2)
    solver.add(drinks[2] == water)
    
    # Clue 14: Carnations arrangement is the root beer lover
    for i in range(5):
        solver.add(z3.Implies(flowers[i] == carnations, drinks[i] == root_beer))
    
    # Clue 15: White color is in second house (index 1)
    solver.add(colors[1] == white)
    
    # Check satisfaction and get model
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Map Z3 constants to string values
        def get_value(z3_var, category_values):
            for val in category_values:
                if str(model.eval(z3_var)) == val:
                    return val
            return None
        
        # Prepare solution rows
        rows = []
        for i in range(5):
            house_num = str(i+1)
            name_val = get_value(names[i], categories['Name'])
            drink_val = get_value(drinks[i], categories['Drink'])
            color_val = get_value(colors[i], categories['Color'])
            flower_val = get_value(flowers[i], categories['Flower'])
            hobby_val = get_value(hobbies[i], categories['Hobby'])
            rows.append([house_num, name_val, drink_val, color_val, flower_val, hobby_val])
        
        # Create JSON output
        solution = {
            "solution": {
                "header": ["House", "Name", "Drink", "Color", "Flower", "Hobby"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()