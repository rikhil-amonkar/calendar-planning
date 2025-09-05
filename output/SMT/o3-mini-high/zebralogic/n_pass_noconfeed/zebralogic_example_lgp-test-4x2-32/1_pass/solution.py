from z3 import *
import json

def main():
    # Create a solver instance
    s = Solver()
    
    # Define person variables (house positions 1 to 4)
    peter = Int('peter')
    arnold = Int('arnold')
    eric = Int('eric')
    alice = Int('alice')
    persons = [peter, arnold, eric, alice]
    
    # Each person is in a house numbered 1 to 4
    for p in persons:
        s.add(And(p >= 1, p <= 4))
    s.add(Distinct(peter, arnold, eric, alice))
    
    # Define pet variables (house positions 1 to 4)
    bird = Int('bird')
    fish = Int('fish')
    dog = Int('dog')
    cat = Int('cat')
    pets = [bird, fish, dog, cat]
    
    for pet in pets:
        s.add(And(pet >= 1, pet <= 4))
    s.add(Distinct(bird, fish, dog, cat))
    
    # Constraint 2: Eric is not in the first house.
    s.add(eric != 1)
    # Constraint 5: Alice is not in the first house.
    s.add(alice != 1)
    
    # Constraint 3: Eric is the person who keeps a pet bird.
    s.add(eric == bird)
    
    # Constraint 6: Arnold is the person with an aquarium of fish.
    s.add(arnold == fish)
    
    # Constraint 4: There is one house between the person with an aquarium of fish and Peter.
    s.add(Or(peter - fish == 2, fish - peter == 2))
    
    # Constraint 1: The person who owns a dog is somewhere to the right of Alice.
    s.add(dog > alice)
    
    # Check if the constraints are satisfiable and extract the model
    if s.check() == sat:
        model = s.model()
        
        # Map each house number to the person living there
        house_to_person = {}
        mapping_person = [(peter, "Peter"), (arnold, "Arnold"), (eric, "Eric"), (alice, "Alice")]
        for var, name in mapping_person:
            pos = model[var].as_long()
            house_to_person[pos] = name
        
        # Map each house number to the pet in that house
        house_to_pet = {}
        mapping_pet = [(bird, "bird"), (fish, "fish"), (dog, "dog"), (cat, "cat")]
        for var, pet_name in mapping_pet:
            pos = model[var].as_long()
            house_to_pet[pos] = pet_name
        
        # Build the rows for each house in order
        rows = []
        for h in range(1, 5):
            rows.append([str(h), house_to_person[h], house_to_pet[h]])
        
        result = {
            "solution": {
                "header": ["House", "Name", "Pet"],
                "rows": rows
            }
        }
        print(json.dumps(result))
    else:
        print(json.dumps({"solution": "No solution found"}))
        
if __name__ == '__main__':
    main()