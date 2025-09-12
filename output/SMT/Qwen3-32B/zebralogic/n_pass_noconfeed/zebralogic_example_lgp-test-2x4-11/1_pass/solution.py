from z3 import *
import json

# Define the EnumSorts
Name, (Eric, Arnold) = EnumSort('Name', ['Eric', 'Arnold'])
Hobby, (Gardening, Photography) = EnumSort('Hobby', ['gardening', 'photography'])
Pet, (Cat, Dog) = EnumSort('Pet', ['cat', 'dog'])
Height, (Short, VeryShort) = EnumSort('Height', ['short', 'very short'])

# Create variables for each house
# House 1
name1 = Const('name1', Name)
hobby1 = Const('hobby1', Hobby)
pet1 = Const('pet1', Pet)
height1 = Const('height1', Height)

# House 2
name2 = Const('name2', Name)
hobby2 = Const('hobby2', Hobby)
pet2 = Const('pet2', Pet)
height2 = Const('height2', Height)

s = Solver()

# Add uniqueness constraints
s.add(name1 != name2)
s.add(hobby1 != hobby2)
s.add(pet1 != pet2)
s.add(height1 != height2)

# Clue 1: If very short, hobby is photography
s.add(Implies(height1 == VeryShort, hobby1 == Photography))
s.add(Implies(height2 == VeryShort, hobby2 == Photography))

# Clue 2: Eric is very short
s.add(Implies(name1 == Eric, height1 == VeryShort))
s.add(Implies(name2 == Eric, height2 == VeryShort))

# Clue 3: cat is to the right of very short person
s.add(pet2 == Cat)
s.add(height1 == VeryShort)

# Check for solution
if s.check() == sat:
    model = s.model()
    
    # Extract values for house 1
    n1 = model[name1].name()
    h1 = model[hobby1].name()
    p1 = model[pet1].name()
    ht1 = model[height1].name()
    
    # House 2
    n2 = model[name2].name()
    h2 = model[hobby2].name()
    p2 = model[pet2].name()
    ht2 = model[height2].name()
    
    # Prepare the JSON structure
    solution = {
        "solution": {
            "header": ["House", "Name", "Hobby", "Pet", "Height"],
            "rows": [
                ["1", n1, h1, p1, ht1],
                ["2", n2, h2, p2, ht2]
            ]
        }
    }
    
    # Print as JSON
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")