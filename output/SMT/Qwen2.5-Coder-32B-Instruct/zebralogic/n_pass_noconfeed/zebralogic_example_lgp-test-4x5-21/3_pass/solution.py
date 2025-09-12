from z3 import *

# Define the variables
names = ["Eric", "Alice", "Peter", "Arnold"]
smoothies = ["dragonfruit", "cherry", "desert", "watermelon"]
sports = ["soccer", "tennis", "basketball", "swimming"]
cars = ["tesla model 3", "toyota camry", "honda civic", "ford f150"]
flowers = ["daffodils", "roses", "lilies", "carnations"]

# Create the solver
solver = Solver()

# Define the arrays for each attribute
house_name = [String(f"house_name_{i}") for i in range(4)]
house_smoothie = [String(f"house_smoothie_{i}") for i in range(4)]
house_sport = [String(f"house_sport_{i}") for i in range(4)]
house_car = [String(f"house_car_{i}") for i in range(4)]
house_flower = [String(f"house_flower_{i}") for i in range(4)]

# Add domain constraints
for i in range(4):
    solver.add(Or(*[house_name[i] == name for name in names]))
    solver.add(Or(*[house_smoothie[i] == smoothie for smoothie in smoothies]))
    solver.add(Or(*[house_sport[i] == sport for sport in sports]))
    solver.add(Or(*[house_car[i] == car for car in cars]))
    solver.add(Or(*[house_flower[i] == flower for flower in flowers]))

# Add uniqueness constraints
solver.add(Distinct(house_name))
solver.add(Distinct(house_smoothie))
solver.add(Distinct(house_sport))
solver.add(Distinct(house_car))
solver.add(Distinct(house_flower))

# Add clue constraints
# 1. The person who owns a Tesla Model 3 is the person who loves the rose bouquet.
solver.add(Implies(house_car[0] == "tesla model 3", house_flower[0] == "roses"))
solver.add(Implies(house_car[1] == "tesla model 3", house_flower[1] == "roses"))
solver.add(Implies(house_car[2] == "tesla model 3", house_flower[2] == "roses"))
solver.add(Implies(house_car[3] == "tesla model 3", house_flower[3] == "roses"))

# 2. Peter is the Dragonfruit smoothie lover.
solver.add(Or([And(house_name[i] == "Peter", house_smoothie[i] == "dragonfruit") for i in range(4)]))

# 3. The Desert smoothie lover is the person who owns a Toyota Camry.
solver.add(Implies(house_smoothie[0] == "desert", house_car[0] == "toyota camry"))
solver.add(Implies(house_smoothie[1] == "desert", house_car[1] == "toyota camry"))
solver.add(Implies(house_smoothie[2] == "desert", house_car[2] == "toyota camry"))
solver.add(Implies(house_smoothie[3] == "desert", house_car[3] == "toyota camry"))

# 4. The person who loves tennis is in the first house.
solver.add(house_sport[0] == "tennis")

# 5. The person who owns a Toyota Camry and the person who loves basketball are next to each other.
solver.add(Or(
    And(house_car[0] == "toyota camry", house_sport[1] == "basketball"),
    And(house_car[1] == "toyota camry", house_sport[0] == "basketball"),
    And(house_car[1] == "toyota camry", house_sport[2] == "basketball"),
    And(house_car[2] == "toyota camry", house_sport[1] == "basketball"),
    And(house_car[2] == "toyota camry", house_sport[3] == "basketball"),
    And(house_car[3] == "toyota camry", house_sport[2] == "basketball")
))

# 6. Arnold is the person who loves basketball.
solver.add(Or([And(house_name[i] == "Arnold", house_sport[i] == "basketball") for i in range(4)]))

# 7. The person who owns a Honda Civic is the person who loves a bouquet of daffodils.
solver.add(Implies(house_car[0] == "honda civic", house_flower[0] == "daffodils"))
solver.add(Implies(house_car[1] == "honda civic", house_flower[1] == "daffodils"))
solver.add(Implies(house_car[2] == "honda civic", house_flower[2] == "daffodils"))
solver.add(Implies(house_car[3] == "honda civic", house_flower[3] == "daffodils"))

# 8. Eric is the person who loves the rose bouquet.
solver.add(Or([And(house_name[i] == "Eric", house_flower[i] == "roses") for i in range(4)]))

# 9. The Watermelon smoothie lover is not in the first house.
solver.add(house_smoothie[0] != "watermelon")

# 10. The person who owns a Honda Civic is somewhere to the right of the Desert smoothie lover.
solver.add(Or(
    And(house_smoothie[0] == "desert", house_car[1] == "honda civic"),
    And(house_smoothie[0] == "desert", house_car[2] == "honda civic"),
    And(house_smoothie[0] == "desert", house_car[3] == "honda civic"),
    And(house_smoothie[1] == "desert", house_car[2] == "honda civic"),
    And(house_smoothie[1] == "desert", house_car[3] == "honda civic"),
    And(house_smoothie[2] == "desert", house_car[3] == "honda civic")
))

# 11. The person who loves basketball is the person who loves the bouquet of lilies.
solver.add(Implies(house_sport[0] == "basketball", house_flower[0] == "lilies"))
solver.add(Implies(house_sport[1] == "basketball", house_flower[1] == "lilies"))
solver.add(Implies(house_sport[2] == "basketball", house_flower[2] == "lilies"))
solver.add(Implies(house_sport[3] == "basketball", house_flower[3] == "lilies"))

# 12. The person who loves tennis and the person who loves soccer are next to each other.
solver.add(Or(
    And(house_sport[0] == "tennis", house_sport[1] == "soccer"),
    And(house_sport[1] == "tennis", house_sport[0] == "soccer"),
    And(house_sport[1] == "tennis", house_sport[2] == "soccer"),
    And(house_sport[2] == "tennis", house_sport[1] == "soccer"),
    And(house_sport[2] == "tennis", house_sport[3] == "soccer"),
    And(house_sport[3] == "tennis", house_sport[2] == "soccer")
))

# Check for a solution
if solver.check() == sat:
    model = solver.model()
    solution = []
    for i in range(4):
        name = model[house_name[i]].as_string()[1:-1]
        smoothie = model[house_smoothie[i]].as_string()[1:-1]
        sport = model[house_sport[i]].as_string()[1:-1]
        car = model[house_car[i]].as_string()[1:-1]
        flower = model[house_flower[i]].as_string()[1:-1]
        solution.append([str(i + 1), name, smoothie, sport, car, flower])

    import json
    print(json.dumps({
        "solution": {
            "header": ["House", "Name", "Smoothie", "FavoriteSport", "CarModel", "Flower"],
            "rows": solution
        }
    }))
else:
    print("No solution found")