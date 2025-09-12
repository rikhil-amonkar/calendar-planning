from z3 import *
import json

def main():
    # Create solver
    solver = Solver()
    
    # Define the houses
    n = 4
    houses = [1, 2, 3, 4]
    
    # Define attributes
    names = ['Peter', 'Arnold', 'Alice', 'Eric']
    flowers = ['roses', 'daffodils', 'carnations', 'lilies']
    hobbies = ['photography', 'painting', 'cooking', 'gardening']
    pets = ['dog', 'fish', 'bird', 'cat']
    colors = ['red', 'yellow', 'green', 'white']
    house_styles = ['craftsman', 'colonial', 'ranch', 'victorian']
    
    # Create dictionaries to store the variables for each attribute
    name_vars = {h: Int(f'name_{h}') for h in houses}
    flower_vars = {h: Int(f'flower_{h}') for h in houses}
    hobby_vars = {h: Int(f'hobby_{h}') for h in houses}
    pet_vars = {h: Int(f'pet_{h}') for h in houses}
    color_vars = {h: Int(f'color_{h}') for h in houses}
    house_style_vars = {h: Int(f'house_style_{h}') for h in houses}
    
    # Each attribute variable must be between 0 and 3 (index of the attribute)
    for h in houses:
        solver.add(name_vars[h] >= 0, name_vars[h] < len(names))
        solver.add(flower_vars[h] >= 0, flower_vars[h] < len(flowers))
        solver.add(hobby_vars[h] >= 0, hobby_vars[h] < len(hobbies))
        solver.add(pet_vars[h] >= 0, pet_vars[h] < len(pets))
        solver.add(color_vars[h] >= 0, color_vars[h] < len(colors))
        solver.add(house_style_vars[h] >= 0, house_style_vars[h] < len(house_styles))
    
    # All attributes are distinct within their category
    solver.add(Distinct([name_vars[h] for h in houses]))
    solver.add(Distinct([flower_vars[h] for h in houses]))
    solver.add(Distinct([hobby_vars[h] for h in houses]))
    solver.add(Distinct([pet_vars[h] for h in houses]))
    solver.add(Distinct([color_vars[h] for h in houses]))
    solver.add(Distinct([house_style_vars[h] for h in houses]))
    
    # Clue 1: The person in a Craftsman-style house is Arnold.
    craftsman_idx = house_styles.index('craftsman')
    arnold_idx = names.index('Arnold')
    solver.add(Exists([h for h in houses], And(house_style_vars[h] == craftsman_idx, name_vars[h] == arnold_idx)))
    
    # Clue 2: The person who loves the rose bouquet is somewhere to the right of Peter.
    roses_idx = flowers.index('roses')
    peter_idx = names.index('Peter')
    solver.add(Exists([h1, h2 for h1 in houses for h2 in houses], 
                     And(name_vars[h1] == peter_idx, flower_vars[h2] == roses_idx, h2 > h1)))
    
    # Clue 3: The photography enthusiast is the person who owns a dog.
    photography_idx = hobbies.index('photography')
    dog_idx = pets.index('dog')
    solver.add(ForAll([h], Implies(hobby_vars[h] == photography_idx, pet_vars[h] == dog_idx)))
    
    # Clue 4: The person who loves a bouquet of daffodils is not in the fourth house.
    daffodils_idx = flowers.index('daffodils')
    solver.add(flower_vars[4] != daffodils_idx)
    
    # Clue 5: The person who loves the rose bouquet is the person whose favorite color is red.
    red_idx = colors.index('red')
    solver.add(ForAll([h], Implies(flower_vars[h] == roses_idx, color_vars[h] == red_idx)))
    
    # Clue 6: The person in a Craftsman-style house is in the second house.
    solver.add(house_style_vars[2] == craftsman_idx)
    
    # Clue 7: Eric is the person residing in a Victorian house.
    eric_idx = names.index('Eric')
    victorian_idx = house_styles.index('victorian')
    solver.add(ForAll([h], Implies(name_vars[h] == eric_idx, house_style_vars[h] == victorian_idx)))
    
    # Clue 8: The person with an aquarium of fish is the person who loves white.
    fish_idx = pets.index('fish')
    white_idx = colors.index('white')
    solver.add(ForAll([h], Implies(pet_vars[h] == fish_idx, color_vars[h] == white_idx)))
    
    # Clue 9: The person who loves cooking is somewhere to the right of the person whose favorite color is red.
    cooking_idx = hobbies.index('cooking')
    solver.add(Exists([h1, h2 for h1 in houses for h2 in houses], 
                     And(color_vars[h1] == red_idx, hobby_vars[h2] == cooking_idx, h2 > h1)))
    
    # Clue 10: The person who loves white is the person who loves a carnations arrangement.
    carnations_idx = flowers.index('carnations')
    solver.add(ForAll([h], Implies(color_vars[h] == white_idx, flower_vars[h] == carnations_idx)))
    
    # Clue 11: The person who loves white is somewhere to the right of the person who enjoys gardening.
    gardening_idx = hobbies.index('gardening')
    solver.add(Exists([h1, h2 for h1 in houses for h2 in houses], 
                     And(hobby_vars[h1] == gardening_idx, color_vars[h2] == white_idx, h2 > h1)))
    
    # Clue 12: The person who loves a bouquet of daffodils is the person who loves yellow.
    yellow_idx = colors.index('yellow')
    solver.add(ForAll([h], Implies(flower_vars[h] == daffodils_idx, color_vars[h] == yellow_idx)))
    
    # Clue 13: The person living in a colonial-style house is the person whose favorite color is red.
    colonial_idx = house_styles.index('colonial')
    solver.add(ForAll([h], Implies(house_style_vars[h] == colonial_idx, color_vars[h] == red_idx)))
    
    # Clue 14: The person who has a cat is Eric.
    cat_idx = pets.index('cat')
    solver.add(ForAll([h], Implies(pet_vars[h] == cat_idx, name_vars[h] == eric_idx)))
    
    # Check if the constraints are satisfiable
    if solver.check() == sat:
        model = solver.model()
        
        # Create result dictionary
        result = {
            "solution": {
                "header": ["House", "Name", "Flower", "Hobby", "Pet", "Color", "HouseStyle"],
                "rows": []
            }
        }
        
        # For each house, get the values of all attributes
        for h in houses:
            name_val = model.evaluate(name_vars[h]).as_long()
            flower_val = model.evaluate(flower_vars[h]).as_long()
            hobby_val = model.evaluate(hobby_vars[h]).as_long()
            pet_val = model.evaluate(pet_vars[h]).as_long()
            color_val = model.evaluate(color_vars[h]).as_long()
            house_style_val = model.evaluate(house_style_vars[h]).as_long()
            
            row = [
                str(h),
                names[name_val],
                flowers[flower_val],
                hobbies[hobby_val],
                pets[pet_val],
                colors[color_val],
                house_styles[house_style_val]
            ]
            result["solution"]["rows"].append(row)
        
        # Output as JSON
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()