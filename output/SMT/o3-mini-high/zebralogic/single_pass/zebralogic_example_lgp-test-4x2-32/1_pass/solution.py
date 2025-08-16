import json
from z3 import Int, Solver, Distinct, Or, Implies

# Create a solver instance
s = Solver()

# Define integer variables for the house positions for each person (houses 1 to 4)
Peter  = Int('Peter')
Arnold = Int('Arnold')
Eric   = Int('Eric')
Alice  = Int('Alice')

# Define integer variables for the pet type for each person.
# We'll encode pets as: 0 = bird, 1 = fish, 2 = dog, 3 = cat.
Peter_pet  = Int('Peter_pet')
Arnold_pet = Int('Arnold_pet')
Eric_pet   = Int('Eric_pet')
Alice_pet  = Int('Alice_pet')

# Constrain house positions to be in the range 1..4
s.add(Peter  >= 1, Peter  <= 4)
s.add(Arnold >= 1, Arnold <= 4)
s.add(Eric   >= 1, Eric   <= 4)
s.add(Alice  >= 1, Alice  <= 4)

# All persons live in different houses
s.add(Distinct(Peter, Arnold, Eric, Alice))

# Constrain pet variables to be in the range 0..3
s.add(Peter_pet  >= 0, Peter_pet  <= 3)
s.add(Arnold_pet >= 0, Arnold_pet <= 3)
s.add(Eric_pet   >= 0, Eric_pet   <= 3)
s.add(Alice_pet  >= 0, Alice_pet  <= 3)

# All persons have different pets
s.add(Distinct(Peter_pet, Arnold_pet, Eric_pet, Alice_pet))

# --- Apply the clues ---

# Clue 2: Eric is not in the first house.
s.add(Eric != 1)

# Clue 5: Alice is not in the first house.
s.add(Alice != 1)

# Clue 3: Eric is the person who keeps a pet bird.
s.add(Eric_pet == 0)  # bird

# Clue 6: Arnold is the person with an aquarium of fish.
s.add(Arnold_pet == 1)  # fish

# Clue 4: There is one house between the person with fish (Arnold) and Peter.
# Using the fact that |Arnold - Peter| = 2.
s.add(Or(Arnold - Peter == 2, Peter - Arnold == 2))

# Clue 1: The person who owns a dog is somewhere to the right of Alice.
# Only one person can have the dog. Since Eric and Arnold already have bird and fish,
# the dog must belong either to Peter or Alice.
# But if Alice had the dog, then the dog's house would equal Alice's house which is not "to the right".
# So we force Alice to not have the dog.
s.add(Alice_pet != 2)  # 2 = dog

# For any person who has the dog, their house must be to the right of Alice.
s.add(Implies(Peter_pet == 2, Peter > Alice))
s.add(Implies(Eric_pet == 2, Eric > Alice))
s.add(Implies(Arnold_pet == 2, Arnold > Alice))
# (Since Alice cannot have dog, no need for an implication there.)

# Given the remaining pet values and the distinct pet constraint,
# it follows that Peter_pet must be 2 (dog) and Alice_pet becomes 3 (cat).

# --- Solve the constraints ---
if s.check().r == 1:  # sat
    m = s.model()
    # Get house assignments
    houses = {
        "Peter":  m[Peter].as_long(),
        "Arnold": m[Arnold].as_long(),
        "Eric":   m[Eric].as_long(),
        "Alice":  m[Alice].as_long()
    }
    # Get pet assignments and map pet codes to names
    pet_codes = {
        "Peter":  m[Peter_pet].as_long(),
        "Arnold": m[Arnold_pet].as_long(),
        "Eric":   m[Eric_pet].as_long(),
        "Alice":  m[Alice_pet].as_long()
    }
    pet_map = {0: "bird", 1: "fish", 2: "dog", 3: "cat"}
    
    # Create a list of rows (house, name, pet) sorted by house number (from left to right)
    rows = []
    for person, house in houses.items():
        rows.append((house, person, pet_map[pet_codes[person]]))
    rows.sort(key=lambda x: x[0])
    
    # Build the JSON structure with the exact required format.
    result = {
      "solution": {
        "header": ["House", "Name", "Pet"],
        "rows": [[str(house), name, pet] for house, name, pet in rows]
      }
    }
    
    # Print the final JSON output
    print(json.dumps(result, indent=2))
else:
    print("No solution found")