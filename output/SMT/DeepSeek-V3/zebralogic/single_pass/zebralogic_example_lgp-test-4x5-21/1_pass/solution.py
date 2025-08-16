from z3 import *

def solve_scheduling_problem():
    # Create a solver instance
    s = Solver()

    # Define the houses
    houses = [1, 2, 3, 4]

    # Define the attributes
    names = ["Eric", "Alice", "Peter", "Arnold"]
    smoothies = ["dragonfruit", "cherry", "desert", "watermelon"]
    sports = ["soccer", "tennis", "basketball", "swimming"]
    car_models = ["tesla model 3", "toyota camry", "honda civic", "ford f150"]
    flowers = ["daffodils", "roses", "lilies", "carnations"]

    # Create dictionaries to hold the variables for each attribute
    name = {house: Int(f"name_{house}") for house in houses}
    smoothie = {house: Int(f"smoothie_{house}") for house in houses}
    sport = {house: Int(f"sport_{house}") for house in houses}
    car_model = {house: Int(f"car_model_{house}") for house in houses}
    flower = {house: Int(f"flower_{house}") for house in houses}

    # Add constraints that each attribute is within the valid range
    for house in houses:
        s.add(name[house] >= 0, name[house] < len(names))
        s.add(smoothie[house] >= 0, smoothie[house] < len(smoothies))
        s.add(sport[house] >= 0, sport[house] < len(sports))
        s.add(car_model[house] >= 0, car_model[house] < len(car_models))
        s.add(flower[house] >= 0, flower[house] < len(flowers))

    # Add constraints that all attributes in each category are distinct
    s.add(Distinct([name[house] for house in houses]))
    s.add(Distinct([smoothie[house] for house in houses]))
    s.add(Distinct([sport[house] for house in houses]))
    s.add(Distinct([car_model[house] for house in houses]))
    s.add(Distinct([flower[house] for house in houses]))

    # Clue 4: The person who loves tennis is in the first house.
    s.add(sport[1] == sports.index("tennis"))

    # Clue 12: The person who loves tennis and the person who loves soccer are next to each other.
    s.add(Or(
        sport[2] == sports.index("soccer"),
        sport[4] == sports.index("soccer")  # House 4 is next to house 3, but house 1 is next to house 2
    ))

    # Clue 5: The person who owns a Toyota Camry and the person who loves basketball are next to each other.
    # We'll handle this after identifying which house has basketball

    # Clue 6: Arnold is the person who loves basketball.
    # So, find the house where sport is basketball and name is Arnold
    for house in houses:
        s.add(Implies(sport[house] == sports.index("basketball"), name[house] == names.index("Arnold")))

    # Clue 11: The person who loves basketball is the person who loves the bouquet of lilies.
    for house in houses:
        s.add(Implies(sport[house] == sports.index("basketball"), flower[house] == flowers.index("lilies")))

    # Clue 2: Peter is the Dragonfruit smoothie lover.
    for house in houses:
        s.add(Implies(name[house] == names.index("Peter"), smoothie[house] == smoothies.index("dragonfruit")))

    # Clue 8: Eric is the person who loves the rose bouquet.
    for house in houses:
        s.add(Implies(name[house] == names.index("Eric"), flower[house] == flowers.index("roses")))

    # Clue 1: The person who owns a Tesla Model 3 is the person who loves the rose bouquet.
    for house in houses:
        s.add(Implies(car_model[house] == car_models.index("tesla model 3"), flower[house] == flowers.index("roses")))

    # Clue 3: The Desert smoothie lover is the person who owns a Toyota Camry.
    for house in houses:
        s.add(Implies(smoothie[house] == smoothies.index("desert"), car_model[house] == car_models.index("toyota camry")))

    # Clue 7: The person who owns a Honda Civic is the person who loves a bouquet of daffodils.
    for house in houses:
        s.add(Implies(car_model[house] == car_models.index("honda civic"), flower[house] == flowers.index("daffodils")))

    # Clue 9: The Watermelon smoothie lover is not in the first house.
    s.add(smoothie[1] != smoothies.index("watermelon"))

    # Clue 10: The person who owns a Honda Civic is somewhere to the right of the Desert smoothie lover.
    # This means the house with Honda Civic has a higher number than the house with Desert smoothie
    for house1 in houses:
        for house2 in houses:
            if house2 <= house1:
                continue
            s.add(Implies(
                And(
                    smoothie[house1] == smoothies.index("desert"),
                    car_model[house2] == car_models.index("honda civic")
                ),
                house2 > house1
            ))

    # Solve the constraints
    if s.check() == sat:
        model = s.model()
        solution = {
            "solution": {
                "header": ["House", "Name", "Smoothie", "FavoriteSport", "CarModel", "Flower"],
                "rows": []
            }
        }
        for house in sorted(houses):
            row = [
                str(house),
                names[model.evaluate(name[house]).as_long()],
                smoothies[model.evaluate(smoothie[house]).as_long()],
                sports[model.evaluate(sport[house]).as_long()],
                car_models[model.evaluate(car_model[house]).as_long()],
                flowers[model.evaluate(flower[house]).as_long()]
            ]
            solution["solution"]["rows"].append(row)
        return solution
    else:
        return {"error": "No solution found"}

# Print the solution in JSON format
import json
print(json.dumps(solve_scheduling_problem(), indent=2))