from z3 import *

# Define variables
names = [Int(f"name_{i}") for i in range(1, 4)]
mothers = [Int(f"mother_{i}") for i in range(1, 4)]
foods = [Int(f"food_{i}") for i in range(1, 4)]

# Define domains
people = ['Eric', 'Peter', 'Arnold']
mothers_names = ['Holly', 'Aniya', 'Janelle']
lunch_foods = ['pizza', 'grilled cheese', 'spaghetti']

# Create a mapping for names, mothers, and foods to integers
name_map = {name: i+1 for i, name in enumerate(people)}
mother_map = {mother: i+1 for i, mother in enumerate(mothers_names)}
food_map = {food: i+1 for i, food in enumerate(lunch_foods)}

# Create reverse mappings for output
reverse_name_map = {v: k for k, v in name_map.items()}
reverse_mother_map = {v: k for k, v in mother_map.items()}
reverse_food_map = {v: k for k, v in food_map.items()}

# Create solver instance
solver = Solver()

# Add constraints for unique values in each category
solver.add(Distinct(names))
solver.add(Distinct(mothers))
solver.add(Distinct(foods))

# Constraint 1: The person who loves spaghetti and Peter are next to each other.
peter_house = Int('peter_house')
solver.add(peter_house == names.index(name_map['Peter']) + 1)
spaghetti_house = Int('spaghetti_house')
solver.add(spaghetti_house == foods.index(food_map['spaghetti']) + 1)
solver.add(Or(peter_house == spaghetti_house + 1, peter_house == spaghetti_house - 1))

# Constraint 2: The person who loves eating grilled cheese is directly left of the person whose mother's name is Aniya.
grilled_cheese_house = Int('grilled_cheese_house')
solver.add(grilled_cheese_house == foods.index(food_map['grilled cheese']) + 1)
aniya_house = Int('aniya_house')
solver.add(aniya_house == mothers.index(mother_map['Aniya']) + 1)
solver.add(grilled_cheese_house == aniya_house - 1)

# Constraint 3: The person who loves eating grilled cheese is Eric.
solver.add(foods[grilled_cheese_house - 1] == name_map['Eric'])

# Constraint 4: Peter is the person whose mother's name is Holly.
solver.add(names[peter_house - 1] == name_map['Peter'])
solver.add(mothers[peter_house - 1] == mother_map['Holly'])

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    solution = []
    for i in range(1, 4):
        name_val = reverse_name_map[model.evaluate(names[i-1]).as_long()]
        mother_val = reverse_mother_map[model.evaluate(mothers[i-1]).as_long()]
        food_val = reverse_food_map[model.evaluate(foods[i-1]).as_long()]
        solution.append([str(i), name_val, mother_val, food_val])
    
    print({
        "solution": {
            "header": ["House", "Name", "Mother", "Food"],
            "rows": solution
        }
    })
else:
    print("No solution found")