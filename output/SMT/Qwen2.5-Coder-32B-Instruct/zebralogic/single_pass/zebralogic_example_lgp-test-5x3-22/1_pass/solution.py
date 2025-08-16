from z3 import *

# Create variables
houses = [Int(f'house_{i}') for i in range(1, 6)]
names = [String(f'name_{i}') for i in range(1, 6)]
smoothies = [String(f'smoothie_{i}') for i in range(1, 6)]
nationalities = [String(f'nationality_{i}') for i in range(1, 6)]

# Define domains
names_domain = ['Arnold', 'Eric', 'Bob', 'Peter', 'Alice']
smoothies_domain = ['desert', 'watermelon', 'lime', 'cherry', 'dragonfruit']
nationalities_domain = ['german', 'swede', 'norwegian', 'dane', 'brit']

# Create solver
solver = Solver()

# Add constraints for unique values in each category
solver.add(Distinct(names))
solver.add(Distinct(smoothies))
solver.add(Distinct(nationalities))

# Add constraints based on clues
# Clue 2: The Dragonfruit smoothie lover is in the second house.
solver.add(smoothies[1] == 'dragonfruit')

# Clue 3: Peter is not in the first house.
solver.add(names[0] != 'Peter')

# Clue 4: The Dane and the British person are next to each other.
dane_house = Int('dane_house')
brit_house = Int('brit_house')
solver.add(Or(dane_house + 1 == brit_house, dane_house - 1 == brit_house))
solver.add(Or(nationalities[i] == 'dane' for i in range(5)))
solver.add(Or(nationalities[i] == 'brit' for i in range(5)))

# Clue 5: The Desert smoothie lover is not in the fifth house.
solver.add(smoothies[4] != 'desert')

# Clue 6: The Swedish person is somewhere to the left of the Dragonfruit smoothie lover.
swede_house = Int('swede_house')
solver.add(Or(nationalities[i] == 'swede' for i in range(5)))
solver.add(swede_house < 1)  # Since dragonfruit is in house 2

# Clue 7: There are two houses between the person who drinks Lime smoothies and the Dane.
lime_house = Int('lime_house')
solver.add(Or(smoothies[i] == 'lime' for i in range(5)))
solver.add(Or(lime_house - dane_house == 3, lime_house - dane_house == -3))

# Clue 8: Bob is the Dane.
solver.add(nationalities[i] == 'dane' for i in range(5) if names[i] == 'Bob')

# Clue 9: Alice is the Norwegian.
solver.add(nationalities[i] == 'norwegian' for i in range(5) if names[i] == 'Alice')

# Clue 10: Alice is in the third house.
solver.add(names[2] == 'Alice')

# Clue 11: The Watermelon smoothie lover is in the third house.
solver.add(smoothies[2] == 'watermelon')

# Map nationalities to houses
for i in range(5):
    solver.add(nationalities[i] == 'dane' if names[i] == 'Bob' else True)
    solver.add(nationalities[i] == 'norwegian' if names[i] == 'Alice' else True)

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = []
    for i in range(5):
        name = model[names[i]].as_string().strip('"')
        smoothie = model[smoothies[i]].as_string().strip('"')
        nationality = model[nationalities[i]].as_string().strip('"')
        solution.append([str(i + 1), name, smoothie, nationality])
    
    print({
        "solution": {
            "header": ["House", "Name", "Smoothie", "Nationality"],
            "rows": solution
        }
    })
else:
    print("No solution found")