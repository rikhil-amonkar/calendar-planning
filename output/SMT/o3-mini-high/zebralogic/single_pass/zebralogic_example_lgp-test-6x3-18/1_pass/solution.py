from z3 import *
import json

# Define the domains:
# Names: "Arnold", "Eric", "Bob", "Alice", "Carol", "Peter"
# We'll assign indices as follows:
# Arnold=0, Eric=1, Bob=2, Alice=3, Carol=4, Peter=5
names_list = ["Arnold", "Eric", "Bob", "Alice", "Carol", "Peter"]

# Mothers: "Sarah", "Holly", "Janelle", "Aniya", "Penny", "Kailyn"
# We'll assign indices as:
# Sarah=0, Holly=1, Janelle=2, Aniya=3, Penny=4, Kailyn=5
mothers_list = ["Sarah", "Holly", "Janelle", "Aniya", "Penny", "Kailyn"]

# Pets: "hamster", "dog", "bird", "cat", "fish", "rabbit"
# We'll assign indices as:
# hamster=0, dog=1, bird=2, cat=3, fish=4, rabbit=5
pets_list = ["hamster", "dog", "bird", "cat", "fish", "rabbit"]

# There are 6 houses (indexed 0..5 for internal representation).
num_houses = 6

# Create Z3 integer variables for each attribute per house.
name_vars = [Int(f"name_{i}") for i in range(num_houses)]
mother_vars = [Int(f"mother_{i}") for i in range(num_houses)]
pet_vars = [Int(f"pet_{i}") for i in range(num_houses)]

s = Solver()

# Each variable must be in the valid domain 0..5.
for i in range(num_houses):
    s.add(And(name_vars[i] >= 0, name_vars[i] < 6))
    s.add(And(mother_vars[i] >= 0, mother_vars[i] < 6))
    s.add(And(pet_vars[i] >= 0, pet_vars[i] < 6))

# All houses have distinct names, distinct mothers, and distinct pets.
s.add(Distinct(name_vars))
s.add(Distinct(mother_vars))
s.add(Distinct(pet_vars))

# --------------------
# Add the clues as constraints:
# Clue 1. Bob is not in the second house.
# Second house is index 1.
# Bob has index 2.
s.add(name_vars[1] != 2)

# Clue 10. Arnold is the person who has a cat.
# Arnold index = 0, cat index = 3.
for i in range(num_houses):
    s.add(Implies(name_vars[i] == 0, pet_vars[i] == 3))
    s.add(Implies(pet_vars[i] == 3, name_vars[i] == 0))

# Clue 7. The person who has a cat is the person whose mother's name is Janelle.
# Janelle's index = 2.
for i in range(num_houses):
    s.add(Implies(pet_vars[i] == 3, mother_vars[i] == 2))
    s.add(Implies(mother_vars[i] == 2, pet_vars[i] == 3))

# Clue 5. The person who owns a rabbit is Eric.
# Rabbit index = 5, Eric index = 1.
for i in range(num_houses):
    s.add(Implies(pet_vars[i] == 5, name_vars[i] == 1))
    s.add(Implies(name_vars[i] == 1, pet_vars[i] == 5))

# Clue 11. The person whose mother's name is Kailyn is the person who owns a rabbit.
# Kailyn index = 5.
for i in range(num_houses):
    s.add(Implies(mother_vars[i] == 5, pet_vars[i] == 5))
    s.add(Implies(pet_vars[i] == 5, mother_vars[i] == 5))

# Clue 12. The person with an aquarium of fish is the person whose mother's name is Sarah.
# fish index = 4, Sarah index = 0.
for i in range(num_houses):
    s.add(Implies(pet_vars[i] == 4, mother_vars[i] == 0))
    s.add(Implies(mother_vars[i] == 0, pet_vars[i] == 4))

# Clue 9. Carol is the person whose mother's name is Aniya.
# Carol index = 4, Aniya index = 3.
for i in range(num_houses):
    s.add(Implies(name_vars[i] == 4, mother_vars[i] == 3))
    s.add(Implies(mother_vars[i] == 3, name_vars[i] == 4))

# Clue 8. Alice is directly left of Carol.
# Alice index = 3, Carol index = 4.
for i in range(num_houses - 1):
    s.add(Implies(name_vars[i] == 3, name_vars[i+1] == 4))
# Also, Alice cannot be in the rightmost house.
s.add(name_vars[num_houses - 1] != 3)

# Clue 3. The person who has a cat is directly left of the person whose mother's name is Holly.
# Holly index = 1.
for i in range(num_houses - 1):
    s.add(Implies(pet_vars[i] == 3, mother_vars[i+1] == 1))
# Cat cannot be in the rightmost house.
s.add(pet_vars[num_houses - 1] != 3)

# Clue 4. The person with a pet hamster is directly left of the person who owns a rabbit.
# hamster index = 0, rabbit index = 5.
for i in range(num_houses - 1):
    s.add(Implies(pet_vars[i] == 0, pet_vars[i+1] == 5))
# Hamster cannot be in the rightmost house.
s.add(pet_vars[num_houses - 1] != 0)

# Clue 2. There are two houses between the person who has a cat and the person who owns a rabbit.
# That is, the distance between the house with cat (3) and the house with rabbit (5) is 3.
for i in range(num_houses):
    for j in range(num_houses):
        s.add(Implies(And(pet_vars[i] == 3, pet_vars[j] == 5),
                      Or(i - j == 3, j - i == 3)))

# Clue 6. There is one house between the person who owns a dog and the person who has a cat.
# Dog index = 1.
for i in range(num_houses):
    for j in range(num_houses):
        s.add(Implies(And(pet_vars[i] == 1, pet_vars[j] == 3),
                      Or(i - j == 2, j - i == 2)))

# --------------------
# Solve and output the solution.

if s.check() == sat:
    m = s.model()
    # Prepare the rows: House numbers should be "1" to "6".
    rows = []
    for i in range(num_houses):
        house_num = str(i + 1)
        person = names_list[m[name_vars[i]].as_long()]
        mother = mothers_list[m[mother_vars[i]].as_long()]
        pet = pets_list[m[pet_vars[i]].as_long()]
        rows.append([house_num, person, mother, pet])
    result = {
        "solution": {
            "header": ["House", "Name", "Mother", "Pet"],
            "rows": rows
        }
    }
    # Print the result as JSON.
    print(json.dumps(result, indent=2))
else:
    print("No solution could be found.")