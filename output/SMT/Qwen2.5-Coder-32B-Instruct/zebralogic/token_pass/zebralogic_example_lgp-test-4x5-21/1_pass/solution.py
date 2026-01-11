from z3 import *

# Define the domains for each variable
names = ['Eric', 'Alice', 'Peter', 'Arnold']
smoothies = ['dragonfruit', 'cherry', 'desert', 'watermelon']
sports = ['soccer', 'tennis', 'basketball', 'swimming']
cars = ['tesla model 3', 'toyota camry', 'honda civic', 'ford f150']
flowers = ['daffodils', 'roses', 'lilies', 'carnations']

# Create variables for each house
house_vars = []
for i in range(4):
    house_vars.append({
        'name': EnumSort(f'name_{i+1}', names)[0],
        'smoothie': EnumSort(f'smoothie_{i+1}', smoothies)[0],
        'sport': EnumSort(f'sport_{i+1}', sports)[0],
        'car': EnumSort(f'car_{i+1}', cars)[0],
        'flower': EnumSort(f'flower_{i+1}', flowers)[0]
    })

# Create a solver instance
solver = Solver()

# Add constraints based on the clues
# Clue 1: The person who owns a Tesla Model 3 is the person who loves the rose bouquet.
solver.add(house_vars[0]['car'] == 'tesla model 3' ==>> house_vars[0]['flower'] == 'roses')
solver.add(house_vars[1]['car'] == 'tesla model 3' ==>> house_vars[1]['flower'] == 'roses')
solver.add(house_vars[2]['car'] == 'tesla model 3' ==>> house_vars[2]['flower'] == 'roses')
solver.add(house_vars[3]['car'] == 'tesla model 3' ==>> house_vars[3]['flower'] == 'roses')

# Clue 2: Peter is the Dragonfruit smoothie lover.
solver.add(house_vars[0]['name'] == 'Peter' ==>> house_vars[0]['smoothie'] == 'dragonfruit')
solver.add(house_vars[1]['name'] == 'Peter' ==>> house_vars[1]['smoothie'] == 'dragonfruit')
solver.add(house_vars[2]['name'] == 'Peter' ==>> house_vars[2]['smoothie'] == 'dragonfruit')
solver.add(house_vars[3]['name'] == 'Peter' ==>> house_vars[3]['smoothie'] == 'dragonfruit')

# Clue 3: The Desert smoothie lover is the person who owns a Toyota Camry.
solver.add(house_vars[0]['smoothie'] == 'desert' ==>> house_vars[0]['car'] == 'toyota camry')
solver.add(house_vars[1]['smoothie'] == 'desert' ==>> house_vars[1]['car'] == 'toyota camry')
solver.add(house_vars[2]['smoothie'] == 'desert' ==>> house_vars[2]['car'] == 'toyota camry')
solver.add(house_vars[3]['smoothie'] == 'desert' ==>> house_vars[3]['car'] == 'toyota camry')

# Clue 4: The person who loves tennis is in the first house.
solver.add(house_vars[0]['sport'] == 'tennis')

# Clue 5: The person who owns a Toyota Camry and the person who loves basketball are next to each other.
solver.add(Or(
    And(house_vars[0]['car'] == 'toyota camry', house_vars[1]['sport'] == 'basketball'),
    And(house_vars[1]['car'] == 'toyota camry', house_vars[0]['sport'] == 'basketball'),
    And(house_vars[1]['car'] == 'toyota camry', house_vars[2]['sport'] == 'basketball'),
    And(house_vars[2]['car'] == 'toyota camry', house_vars[1]['sport'] == 'basketball'),
    And(house_vars[2]['car'] == 'toyota camry', house_vars[3]['sport'] == 'basketball'),
    And(house_vars[3]['car'] == 'toyota camry', house_vars[2]['sport'] == 'basketball')
))

# Clue 6: Arnold is the person who loves basketball.
solver.add(house_vars[0]['name'] == 'Arnold' ==>> house_vars[0]['sport'] == 'basketball')
solver.add(house_vars[1]['name'] == 'Arnold' ==>> house_vars[1]['sport'] == 'basketball')
solver.add(house_vars[2]['name'] == 'Arnold' ==>> house_vars[2]['sport'] == 'basketball')
solver.add(house_vars[3]['name'] == 'Arnold' ==>> house_vars[3]['sport'] == 'basketball')

# Clue 7: The person who owns a Honda Civic is the person who loves a bouquet of daffodils.
solver.add(house_vars[0]['car'] == 'honda civic' ==>> house_vars[0]['flower'] == 'daffodils')
solver.add(house_vars[1]['car'] == 'honda civic' ==>> house_vars[1]['flower'] == 'daffodils')
solver.add(house_vars[2]['car'] == 'honda civic' ==>> house_vars[2]['flower'] == 'daffodils')
solver.add(house_vars[3]['car'] == 'honda civic' ==>> house_vars[3]['flower'] == 'daffodils')

# Clue 8: Eric is the person who loves the rose bouquet.
solver.add(house_vars[0]['name'] == 'Eric' ==>> house_vars[0]['flower'] == 'roses')
solver.add(house_vars[1]['name'] == 'Eric' ==>> house_vars[1]['flower'] == 'roses')
solver.add(house_vars[2]['name'] == 'Eric' ==>> house_vars[2]['flower'] == 'roses')
solver.add(house_vars[3]['name'] == 'Eric' ==>> house_vars[3]['flower'] == 'roses')

# Clue 9: The Watermelon smoothie lover is not in the first house.
solver.add(house_vars[0]['smoothie'] != 'watermelon')

# Clue 10: The person who owns a Honda Civic is somewhere to the right of the Desert smoothie lover.
solver.add(Or(
    And(house_vars[0]['smoothie'] == 'desert', house_vars[1]['car'] == 'honda civic'),
    And(house_vars[0]['smoothie'] == 'desert', house_vars[2]['car'] == 'honda civic'),
    And(house_vars[0]['smoothie'] == 'desert', house_vars[3]['car'] == 'honda civic'),
    And(house_vars[1]['smoothie'] == 'desert', house_vars[2]['car'] == 'honda civic'),
    And(house_vars[1]['smoothie'] == 'desert', house_vars[3]['car'] == 'honda civic'),
    And(house_vars[2]['smoothie'] == 'desert', house_vars[3]['car'] == 'honda civic')
))

# Clue 11: The person who loves basketball is the person who loves the bouquet of lilies.
solver.add(house_vars[0]['sport'] == 'basketball' ==>> house_vars[0]['flower'] == 'lilies')
solver.add(house_vars[1]['sport'] == 'basketball' ==>> house_vars[1]['flower'] == 'lilies')
solver.add(house_vars[2]['sport'] == 'basketball' ==>> house_vars[2]['flower'] == 'lilies')
solver.add(house_vars[3]['sport'] == 'basketball' ==>> house_vars[3]['flower'] == 'lilies')

# Clue 12: The person who loves tennis and the person who loves soccer are next to each other.
solver.add(Or(
    And(house_vars[0]['sport'] == 'tennis', house_vars[1]['sport'] == 'soccer'),
    And(house_vars[1]['sport'] == 'tennis', house_vars[0]['sport'] == 'soccer'),
    And(house_vars[1]['sport'] == 'tennis', house_vars[2]['sport'] == 'soccer'),
    And(house_vars[2]['sport'] == 'tennis', house_vars[1]['sport'] == 'soccer'),
    And(house_vars[2]['sport'] == 'tennis', house_vars[3]['sport'] == 'soccer'),
    And(house_vars[3]['sport'] == 'tennis', house_vars[2]['sport'] == 'soccer')
))

# Ensure all names, smoothies, sports, cars, and flowers are unique
solver.add(Distinct([house_vars[i]['name'] for i in range(4)]))
solver.add(Distinct([house_vars[i]['smoothie'] for i in range(4)]))
solver.add(Distinct([house_vars[i]['sport'] for i in range(4)]))
solver.add(Distinct([house_vars[i]['car'] for i in range(4)]))
solver.add(Distinct([house_vars[i]['flower'] for i in range(4)]))

# Check if the problem is solvable
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "FavoriteSport", "CarModel", "Flower"],
            "rows": []
        }
    }
    for i in range(4):
        house_solution = [
            str(i + 1),
            model[house_vars[i]['name']].as_string(),
            model[house_vars[i]['smoothie']].as_string(),
            model[house_vars[i]['sport']].as_string(),
            model[house_vars[i]['car']].as_string(),
            model[house_vars[i]['flower']].as_string()
        ]
        solution["solution"]["rows"].append(house_solution)
    
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")