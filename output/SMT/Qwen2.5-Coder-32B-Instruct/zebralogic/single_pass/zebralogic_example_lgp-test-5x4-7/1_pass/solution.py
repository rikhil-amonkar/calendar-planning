from z3 import *

# Create a solver instance
solver = Solver()

# Define variables
houses = [Int(f"house_{i}") for i in range(1, 6)]
names = ["Alice", "Peter", "Bob", "Eric", "Arnold"]
smoothies = ["lime", "dragonfruit", "desert", "watermelon", "cherry"]
animals = ["horse", "dog", "bird", "fish", "cat"]
nationalities = ["german", "swede", "norwegian", "brit", "dane"]

# Create dictionaries to map each attribute to a variable
name_vars = {name: Int(name) for name in names}
smoothie_vars = {smoothie: Int(smoothie) for smoothie in smoothies}
animal_vars = {animal: Int(animal) for animal in animals}
nationality_vars = {nationality: Int(nationality) for nationality in nationalities}

# Add constraints that each attribute is assigned to a unique house
solver.add(Distinct(houses))
solver.add(Distinct(list(name_vars.values())))
solver.add(Distinct(list(smoothie_vars.values())))
solver.add(Distinct(list(animal_vars.values())))
solver.add(Distinct(list(nationality_vars.values())))

# Add constraints based on the clues
# 1. The Swedish person is directly left of the dog owner.
solver.add(nationality_vars["swede"] + 1 == animal_vars["dog"])

# 2. There are two houses between the dog owner and the British person.
solver.add(Abs(animal_vars["dog"] - nationality_vars["brit"]) == 3)

# 3. The Dane is the person who keeps horses.
solver.add(nationality_vars["dane"] == animal_vars["horse"])

# 4. The bird keeper is somewhere to the right of the cat lover.
solver.add(animal_vars["bird"] > animal_vars["cat"])

# 5. The dog owner is directly left of the person who drinks Lime smoothies.
solver.add(animal_vars["dog"] + 1 == smoothie_vars["lime"])

# 6. Eric is the cat lover.
solver.add(name_vars["Eric"] == animal_vars["cat"])

# 7. Bob is the bird keeper.
solver.add(name_vars["Bob"] == animal_vars["bird"])

# 8. The person who likes Cherry smoothies is directly left of Peter.
solver.add(smoothie_vars["cherry"] + 1 == name_vars["Peter"])

# 9. The bird keeper is the Watermelon smoothie lover.
solver.add(animal_vars["bird"] == smoothie_vars["watermelon"])

# 10. The Desert smoothie lover is the dog owner.
solver.add(smoothie_vars["desert"] == animal_vars["dog"])

# 11. The person who keeps horses is in the third house.
solver.add(animal_vars["horse"] == 3)

# 12. The Norwegian is Alice.
solver.add(nationality_vars["norwegian"] == name_vars["Alice"])

# Solve the problem
if solver.check() == sat:
    model = solver.model()
    # Create a mapping from house number to attributes
    house_to_attributes = {str(i): [] for i in range(1, 6)}
    for name, var in name_vars.items():
        house_number = model[var].as_long()
        house_to_attributes[str(house_number)].append(name)
    for smoothie, var in smoothie_vars.items():
        house_number = model[var].as_long()
        house_to_attributes[str(house_number)].append(smoothie)
    for animal, var in animal_vars.items():
        house_number = model[var].as_long()
        house_to_attributes[str(house_number)].append(animal)
    for nationality, var in nationality_vars.items():
        house_number = model[var].as_long()
        house_to_attributes[str(house_number)].append(nationality)

    # Prepare the solution in the required format
    solution = {
        "solution": {
            "header": ["House", "Name", "Smoothie", "Animal", "Nationality"],
            "rows": [[house] + attributes for house, attributes in house_to_attributes.items()]
        }
    }

    # Print the solution
    import json
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")