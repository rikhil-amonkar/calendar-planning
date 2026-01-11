from z3 import *

# Define the solver
solver = Solver()

# Define the variables for each characteristic of each person in each house
names = ['Arnold', 'Eric']
sports = ['basketball', 'soccer']
hair_colors = ['brown', 'black']
heights = ['very short', 'short']
smoothies = ['desert', 'cherry']
flowers = ['daffodils', 'carnations']

# Create symbolic variables for each characteristic of each person in each house
house1_name = String('house1_name')
house1_sport = String('house1_sport')
house1_hair_color = String('house1_hair_color')
house1_height = String('house1_height')
house1_smoothie = String('house1_smoothie')
house1_flower = String('house1_flower')

house2_name = String('house2_name')
house2_sport = String('house2_sport')
house2_hair_color = String('house2_hair_color')
house2_height = String('house2_height')
house2_smoothie = String('house2_smoothie')
house2_flower = String('house2_flower')

# Add constraints for unique values for each characteristic in each house
solver.add(house1_name != house2_name)
solver.add(house1_sport != house2_sport)
solver.add(house1_hair_color != house2_hair_color)
solver.add(house1_height != house2_height)
solver.add(house1_smoothie != house2_smoothie)
solver.add(house1_flower != house2_flower)

# Add constraints for each characteristic to be one of the possible values
solver.add(Or(house1_name == 'Arnold', house1_name == 'Eric'))
solver.add(Or(house2_name == 'Arnold', house2_name == 'Eric'))

solver.add(Or(house1_sport == 'basketball', house1_sport == 'soccer'))
solver.add(Or(house2_sport == 'basketball', house2_sport == 'soccer'))

solver.add(Or(house1_hair_color == 'brown', house1_hair_color == 'black'))
solver.add(Or(house2_hair_color == 'brown', house2_hair_color == 'black'))

solver.add(Or(house1_height == 'very short', house1_height == 'short'))
solver.add(Or(house2_height == 'very short', house2_height == 'short'))

solver.add(Or(house1_smoothie == 'desert', house1_smoothie == 'cherry'))
solver.add(Or(house2_smoothie == 'desert', house2_smoothie == 'cherry'))

solver.add(Or(house1_flower == 'daffodils', house1_flower == 'carnations'))
solver.add(Or(house2_flower == 'daffodils', house2_flower == 'carnations'))

# Apply the clues
# Clue 1: The person who loves soccer is not in the second house.
solver.add(house2_sport != 'soccer')

# Clue 2: The Desert smoothie lover is directly left of the person who is very short.
solver.add(Implies(house1_smoothie == 'desert', house2_height == 'very short'))
solver.add(Implies(house2_smoothie == 'desert', house1_height == 'very short'))

# Clue 3: The person who is very short is the person who has brown hair.
solver.add(Implies(house1_height == 'very short', house1_hair_color == 'brown'))
solver.add(Implies(house2_height == 'very short', house2_hair_color == 'brown'))

# Clue 4: The person who loves a carnation arrangement is the Desert smoothie lover.
solver.add(Implies(house1_smoothie == 'desert', house1_flower == 'carnations'))
solver.add(Implies(house2_smoothie == 'desert', house2_flower == 'carnations'))

# Clue 5: Eric and the person who has brown hair are next to each other.
solver.add(Or((house1_name == 'Eric' & house2_hair_color == 'brown'), 
             (house2_name == 'Eric' & house1_hair_color == 'brown')))

# Check if the constraints are satisfiable
if solver.check() == sat:
    model = solver.model()
    # Extract the solution
    house1_solution = [model[house1_name].as_string(), model[house1_sport].as_string(),
                       model[house1_hair_color].as_string(), model[house1_height].as_string(),
                       model[house1_smoothie].as_string(), model[house1_flower].as_string()]
    
    house2_solution = [model[house2_name].as_string(), model[house2_sport].as_string(),
                       model[house2_hair_color].as_string(), model[house2_height].as_string(),
                       model[house2_smoothie].as_string(), model[house2_flower].as_string()]
    
    # Format the solution as required
    solution = {
        "solution": {
            "header": ["House", "Name", "FavoriteSport", "HairColor", "Height", "Smoothie", "Flower"],
            "rows": [
                ["1"] + house1_solution,
                ["2"] + house2_solution
            ]
        }
    }
    print(solution)
else:
    print("No solution found")