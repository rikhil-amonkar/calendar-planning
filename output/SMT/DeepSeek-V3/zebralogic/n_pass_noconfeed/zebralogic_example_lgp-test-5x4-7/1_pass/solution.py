import z3
import json

def main():
    solver = z3.Solver()
    
    # Define the attributes and their possible values
    names = ['Alice', 'Peter', 'Bob', 'Eric', 'Arnold']
    smoothies = ['lime', 'dragonfruit', 'desert', 'watermelon', 'cherry']
    animals = ['horse', 'dog', 'bird', 'fish', 'cat']
    nationalities = ['german', 'swede', 'norwegian', 'brit', 'dane']
    
    # Create integer variables for each attribute (1-5)
    name_vars = [z3.Int(f'name_{name}') for name in names]
    smoothie_vars = [z3.Int(f'smoothie_{smoothie}') for smoothie in smoothies]
    animal_vars = [z3.Int(f'animal_{animal}') for animal in animals]
    nationality_vars = [z3.Int(f'nationality_{nat}') for nat in nationalities]
    
    # All attributes must be between 1 and 5 (house numbers)
    for var in name_vars + smoothie_vars + animal_vars + nationality_vars:
        solver.add(z3.And(var >= 1, var <= 5))
    
    # All attributes of the same type must have distinct values
    solver.add(z3.Distinct(name_vars))
    solver.add(z3.Distinct(smoothie_vars))
    solver.add(z3.Distinct(animal_vars))
    solver.add(z3.Distinct(nationality_vars))
    
    # Create helper variables for easier constraint writing
    swede = nationality_vars[nationalities.index('swede')]
    brit = nationality_vars[nationalities.index('brit')]
    dane = nationality_vars[nationalities.index('dane')]
    norwegian = nationality_vars[nationalities.index('norwegian')]
    
    dog_owner = animal_vars[animals.index('dog')]
    horse_owner = animal_vars[animals.index('horse')]
    bird_owner = animal_vars[animals.index('bird')]
    cat_owner = animal_vars[animals.index('cat')]
    
    lime_smoothie = smoothie_vars[smoothies.index('lime')]
    desert_smoothie = smoothie_vars[smoothies.index('desert')]
    watermelon_smoothie = smoothie_vars[smoothies.index('watermelon')]
    cherry_smoothie = smoothie_vars[smoothies.index('cherry')]
    
    alice = name_vars[names.index('Alice')]
    peter = name_vars[names.index('Peter')]
    bob = name_vars[names.index('Bob')]
    eric = name_vars[names.index('Eric')]
    arnold = name_vars[names.index('Arnold')]
    
    # Apply the constraints
    # 1. The Swedish person is directly left of the dog owner.
    solver.add(swede == dog_owner - 1)
    
    # 2. There are two houses between the dog owner and the British person.
    solver.add(z3.Or(dog_owner == brit - 3, dog_owner == brit + 3))
    
    # 3. The Dane is the person who keeps horses.
    solver.add(dane == horse_owner)
    
    # 4. The bird keeper is somewhere to the right of the cat lover.
    solver.add(bird_owner > cat_owner)
    
    # 5. The dog owner is directly left of the person who drinks Lime smoothies.
    solver.add(dog_owner == lime_smoothie - 1)
    
    # 6. Eric is the cat lover.
    solver.add(eric == cat_owner)
    
    # 7. Bob is the bird keeper.
    solver.add(bob == bird_owner)
    
    # 8. The person who likes Cherry smoothies is directly left of Peter.
    solver.add(cherry_smoothie == peter - 1)
    
    # 9. The bird keeper is the Watermelon smoothie lover.
    solver.add(bird_owner == watermelon_smoothie)
    
    # 10. The Desert smoothie lover is the dog owner.
    solver.add(desert_smoothie == dog_owner)
    
    # 11. The person who keeps horses is in the third house.
    solver.add(horse_owner == 3)
    
    # 12. The Norwegian is Alice.
    solver.add(norwegian == alice)
    
    # Check if the constraints are satisfiable
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Create result dictionaries
        house_data = {i: {} for i in range(1, 6)}
        
        # Extract values for each attribute
        for i, name in enumerate(names):
            house_num = model.eval(name_vars[i]).as_long()
            house_data[house_num]['Name'] = name
            
        for i, smoothie in enumerate(smoothies):
            house_num = model.eval(smoothie_vars[i]).as_long()
            house_data[house_num]['Smoothie'] = smoothie
            
        for i, animal in enumerate(animals):
            house_num = model.eval(animal_vars[i]).as_long()
            house_data[house_num]['Animal'] = animal
            
        for i, nationality in enumerate(nationalities):
            house_num = model.eval(nationality_vars[i]).as_long()
            house_data[house_num]['Nationality'] = nationality
        
        # Prepare the output in the required format
        rows = []
        for house_num in range(1, 6):
            data = house_data[house_num]
            rows.append([
                str(house_num),
                data['Name'],
                data['Smoothie'],
                data['Animal'],
                data['Nationality']
            ])
        
        result = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "Animal", "Nationality"],
                "rows": rows
            }
        }
        
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No solution found"}')

if __name__ == "__main__":
    main()