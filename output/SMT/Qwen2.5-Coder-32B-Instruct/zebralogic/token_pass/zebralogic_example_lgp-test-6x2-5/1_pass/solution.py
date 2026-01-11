from z3 import *

# Define the domain of possible values
names = ['Bob', 'Peter', 'Alice', 'Eric', 'Carol', 'Arnold']
vacations = ['mountain', 'camping', 'cruise', 'city', 'cultural', 'beach']

# Create variables for each house
house_vars = []
for i in range(1, 7):
    house_name = Int(f'house_{i}_name')
    house_vacation = Int(f'house_{i}_vacation')
    house_vars.append((house_name, house_vacation))

# Create a solver instance
solver = Solver()

# Add constraints for unique assignments
solver.add(Distinct([house_name for house_name, _ in house_vars]))
solver.add(Distinct([house_vacation for _, house_vacation in house_vars]))

# Map names and vacations to integers
name_map = {name: i for i, name in enumerate(names)}
vacation_map = {vacation: i for i, vacation in enumerate(vacations)}

# Encode the clues as constraints
# Clue 1 & 7: Peter (cultural) is in the third house
solver.add(house_vars[2][0] == name_map['Peter'])
solver.add(house_vars[2][1] == vacation_map['cultural'])

# Clue 2: Eric is in the second house
solver.add(house_vars[1][0] == name_map['Eric'])

# Clue 3: Eric is to the right of Alice
alice_house = Int('alice_house')
solver.add(Or([house_vars[i][0] == name_map['Alice'] for i in range(6)]))
solver.add(And([If(house_vars[i][0] == name_map['Alice'], alice_house == i, True) for i in range(6)]))
solver.add(alice_house < 1)  # Eric is in house 2, so Alice must be in house 1

# Clue 4: Beach vacation is to the right of cultural (Peter)
beach_house = Int('beach_house')
solver.add(Or([house_vars[i][1] == vacation_map['beach'] for i in range(6)]))
solver.add(And([If(house_vars[i][1] == vacation_map['beach'], beach_house == i, True) for i in range(6)]))
solver.add(beach_house > 2)

# Clue 5: Bob is directly left of Arnold
bob_house = Int('bob_house')
arnold_house = Int('arnold_house')
solver.add(Or([house_vars[i][0] == name_map['Bob'] for i in range(6)]))
solver.add(Or([house_vars[i][0] == name_map['Arnold'] for i in range(6)]))
solver.add(And([If(house_vars[i][0] == name_map['Bob'], bob_house == i, True) for i in range(6)]))
solver.add(And([If(house_vars[i][0] == name_map['Arnold'], arnold_house == i, True) for i in range(6)]))
solver.add(bob_house + 1 == arnold_house)

# Clue 6: Camping is not in the first house
solver.add(house_vars[0][1] != vacation_map['camping'])

# Clue 8: Bob's vacation is cruise
solver.add(house_vars[bob_house][1] == vacation_map['cruise'])

# Clue 9: City break is in the fourth house
solver.add(house_vars[3][1] == vacation_map['city'])

# Check if the constraints are satisfiable and get the model
if solver.check() == sat:
    model = solver.model()
    solution = {
        "solution": {
            "header": ["House", "Name", "Vacation"],
            "rows": []
        }
    }
    for i, (house_name, house_vacation) in enumerate(house_vars):
        name = names[model.evaluate(house_name).as_long()]
        vacation = vacations[model.evaluate(house_vacation).as_long()]
        solution["solution"]["rows"].append([str(i+1), name, vacation])
    
    print(solution)
else:
    print("No solution found")