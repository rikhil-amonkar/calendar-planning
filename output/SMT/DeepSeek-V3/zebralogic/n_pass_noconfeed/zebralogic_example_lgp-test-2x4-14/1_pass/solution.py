import z3
import json

def main():
    solver = z3.Solver()
    
    # Define the houses
    houses = [1, 2]
    
    # Define attributes
    names = ['Eric', 'Arnold']
    house_styles = ['victorian', 'colonial']
    smoothies = ['cherry', 'desert']
    pets = ['dog', 'cat']
    
    # Create variables for each attribute per house
    name_vars = {house: z3.Int(f'name_{house}') for house in houses}
    style_vars = {house: z3.Int(f'style_{house}') for house in houses}
    smoothie_vars = {house: z3.Int(f'smoothie_{house}') for house in houses}
    pet_vars = {house: z3.Int(f'pet_{house}') for house in houses}
    
    # Define domains for each attribute
    for house in houses:
        solver.add(z3.And(name_vars[house] >= 0, name_vars[house] < len(names)))
        solver.add(z3.And(style_vars[house] >= 0, style_vars[house] < len(house_styles)))
        solver.add(z3.And(smoothie_vars[house] >= 0, smoothie_vars[house] < len(smoothies)))
        solver.add(z3.And(pet_vars[house] >= 0, pet_vars[house] < len(pets)))
    
    # All attributes are unique per category
    solver.add(z3.Distinct([name_vars[house] for house in houses]))
    solver.add(z3.Distinct([style_vars[house] for house in houses]))
    solver.add(z3.Distinct([smoothie_vars[house] for house in houses]))
    solver.add(z3.Distinct([pet_vars[house] for house in houses]))
    
    # Clue 1: The person who likes Cherry smoothies is the person who owns a dog.
    cherry_index = smoothies.index('cherry')
    dog_index = pets.index('dog')
    for house in houses:
        solver.add(z3.Implies(smoothie_vars[house] == cherry_index, pet_vars[house] == dog_index))
    
    # Clue 2: The person residing in a Victorian house is the person who owns a dog.
    victorian_index = house_styles.index('victorian')
    for house in houses:
        solver.add(z3.Implies(style_vars[house] == victorian_index, pet_vars[house] == dog_index))
    
    # Clue 3: The person residing in a Victorian house is somewhere to the left of Eric.
    eric_index = names.index('Eric')
    victorian_house = None
    eric_house = None
    
    # Find which house has Victorian style and which has Eric
    for house in houses:
        # Victorian house constraint
        solver.add(z3.Implies(style_vars[house] == victorian_index, z3.And(house < 2)))  # Victorian is left of Eric, so must be house 1
        
        # Eric constraint - must be in house 2 if Victorian is in house 1
        solver.add(z3.Implies(name_vars[house] == eric_index, house == 2))
    
    # Check if solution exists
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Prepare result data
        result = {
            "solution": {
                "header": ["House", "Name", "HouseStyle", "Smoothie", "Pet"],
                "rows": []
            }
        }
        
        for house in sorted(houses):
            name_idx = model.evaluate(name_vars[house]).as_long()
            style_idx = model.evaluate(style_vars[house]).as_long()
            smoothie_idx = model.evaluate(smoothie_vars[house]).as_long()
            pet_idx = model.evaluate(pet_vars[house]).as_long()
            
            row = [
                str(house),
                names[name_idx],
                house_styles[style_idx],
                smoothies[smoothie_idx],
                pets[pet_idx]
            ]
            result["solution"]["rows"].append(row)
        
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()