from z3 import *

# Create variables
houses = [Int(f"house_{i}") for i in range(1, 6)]
names = [String(f"name_{i}") for i in range(1, 6)]
drinks = [String(f"drink_{i}") for i in range(1, 6)]
colors = [String(f"color_{i}") for i in range(1, 6)]
flowers = [String(f"flower_{i}") for i in range(1, 6)]
hobbies = [String(f"hobby_{i}") for i in range(1, 6)]

# Define domains
people = ["Bob", "Arnold", "Peter", "Alice", "Eric"]
beverages = ["milk", "root beer", "coffee", "tea", "water"]
colours = ["blue", "green", "white", "yellow", "red"]
blooms = ["daffodils", "roses", "lilies", "tulips", "carnations"]
pastimes = ["painting", "cooking", "photography", "gardening", "knitting"]

# Create solver
solver = Solver()

# Add constraints for uniqueness
solver.add(Distinct(names))
solver.add(Distinct(drinks))
solver.add(Distinct(colors))
solver.add(Distinct(flowers))
solver.add(Distinct(hobbies))

# Add specific clues
solver.add(Not(names[3] == "Alice"))  # Alice is not in the fourth house.
solver.add(And(drinks[i] == "root beer", hobbies[i] == "gardening") for i in range(5))  # The root beer lover is the person who enjoys gardening.
solver.add(And(colors[i] == "green", drinks[i] == "coffee") for i in range(5))  # The person whose favorite color is green is the coffee drinker.
solver.add(And(colors[i] == "green", flowers[i] == "lilies") for i in range(5))  # The person whose favorite color is green is the person who loves the boquet of lilies.
solver.add(Or([colors[j] == "blue" for j in range(i+1, 5)]) for i in range(5) if colors[i] == "daffodils")  # The person who loves blue is somewhere to the right of the person who loves a bouquet of daffodils.
solver.add(And(colors[i] == "blue", hobbies[i] == "cooking") for i in range(5))  # The person who loves cooking is the person who loves blue.
solver.add(And(names[i] == "Eric", drinks[i+1] == "tea") for i in range(4))  # Eric is directly left of the tea drinker.
solver.add(And(names[i] == "Peter", drinks[i] == "water") for i in range(5))  # The one who only drinks water is Peter.
solver.add(And(names[i] == "Arnold", hobbies[i] == "photography") for i in range(5))  # Arnold is the photography enthusiast.
solver.add(And(colors[i] == "white", flowers[i] == "roses") for i in range(5))  # The person who loves white is the person who loves the rose bouquet.
solver.add(Or([And(flowers[j] == "carnations", colors[i] == "red") for j in range(max(0, i-1), min(i+2, 5))]) for i in range(5))  # There is one house between the person who loves a carnations arrangement and the person whose favorite color is red.
solver.add(Or([And(hobbies[j] == "painting", hobbies[i] == "cooking") for j in range(i+1, 5)]) for i in range(5))  # The person who loves cooking is somewhere to the left of the person who paints as a hobby.
solver.add(And(names[i] == "Peter", houses[i] == 3) for i in range(5))  # The one who only drinks water is in the third house.
solver.add(And(drinks[i] == "root beer", flowers[i] == "carnations") for i in range(5))  # The person who loves a carnations arrangement is the root beer lover.
solver.add(And(colors[i] == "white", houses[i] == 2) for i in range(5))  # The person who loves white is in the second house.

# Check if the solution exists
if solver.check() == sat:
    model = solver.model()
    solution = []
    for i in range(5):
        house = str(i + 1)
        name = model[names[i]].as_string()[1:-1]
        drink = model[drinks[i]].as_string()[1:-1]
        color = model[colors[i]].as_string()[1:-1]
        flower = model[flowers[i]].as_string()[1:-1]
        hobby = model[hobbies[i]].as_string()[1:-1]
        solution.append([house, name, drink, color, flower, hobby])
    
    print({
        "solution": {
            "header": ["House", "Name", "Drink", "Color", "Flower", "Hobby"],
            "rows": solution
        }
    })
else:
    print("No solution found")