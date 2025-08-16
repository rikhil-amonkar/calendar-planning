from z3 import *
import json

# Create an optimizer (or solver)
s = Solver()

# We represent the house number (1,2,3) for each person, mother and food.
# Persons
Eric = Int('Eric')
Peter = Int('Peter')
Arnold = Int('Arnold')

# Mothers
Holly = Int('Holly')
Aniya = Int('Aniya')
Janelle = Int('Janelle')

# Foods
grilled = Int('grilled')    # the one who eats grilled cheese
pizza = Int('pizza')
spaghetti = Int('spaghetti')

houses = [1, 2, 3]

# Add domain constraints (each must be between 1 and 3)
all_vars = [Eric, Peter, Arnold, Holly, Aniya, Janelle, grilled, pizza, spaghetti]
for var in all_vars:
    s.add(var >= 1, var <= 3)

# All in the same category are in different houses
s.add(Distinct(Eric, Peter, Arnold))
s.add(Distinct(Holly, Aniya, Janelle))
s.add(Distinct(grilled, pizza, spaghetti))

# Clue 3: The person who loves eating grilled cheese is Eric.
# So, the house of Eric equals the house that has grilled cheese.
s.add(Eric == grilled)

# Clue 4: Peter is the person whose mother's name is Holly.
# So, Peter must be in the same house as Holly.
s.add(Peter == Holly)

# Clue 2: The person who loves eating grilled cheese (Eric) is directly left of the person whose mother's name is Aniya.
# "Directly left" means: house(Eric) + 1 = house(Aniya)
s.add(Eric != 3)  # Eric can't be in house 3 because he needs a house to his right
s.add(Aniya == Eric + 1)

# Clue 1: The spaghetti eater and Peter are next to each other.
# The spaghetti eater is the person in the house where Food == spaghetti.
s.add(Or(spaghetti == Peter + 1, spaghetti == Peter - 1))

# Check the solver
if s.check() == sat:
    m = s.model()
    # Construct the solution for houses 1, 2, 3.
    # We need to invert our variables: each attribute takes a house number.
    # For each house, we decide which person, which mother and which food is there.
    
    # Create dictionaries for each category mapping house number to the attribute name.
    person_at = {}
    mother_at = {}
    food_at = {}
    
    # Persons:
    if m.evaluate(Eric).as_long() in houses:
        person_at[m.evaluate(Eric).as_long()] = "Eric"
    if m.evaluate(Peter).as_long() in houses:
        person_at[m.evaluate(Peter).as_long()] = "Peter"
    if m.evaluate(Arnold).as_long() in houses:
        person_at[m.evaluate(Arnold).as_long()] = "Arnold"
    
    # Mothers:
    if m.evaluate(Holly).as_long() in houses:
        mother_at[m.evaluate(Holly).as_long()] = "Holly"
    if m.evaluate(Aniya).as_long() in houses:
        mother_at[m.evaluate(Aniya).as_long()] = "Aniya"
    if m.evaluate(Janelle).as_long() in houses:
        mother_at[m.evaluate(Janelle).as_long()] = "Janelle"
    
    # Foods:
    if m.evaluate(grilled).as_long() in houses:
        food_at[m.evaluate(grilled).as_long()] = "grilled cheese"
    if m.evaluate(pizza).as_long() in houses:
        food_at[m.evaluate(pizza).as_long()] = "pizza"
    if m.evaluate(spaghetti).as_long() in houses:
        food_at[m.evaluate(spaghetti).as_long()] = "spaghetti"
    
    # Now build the ordered solution (houses 1,2,3)
    rows = []
    for house in sorted(houses):
        row = [str(house),
               person_at[house],
               mother_at[house],
               food_at[house]]
        rows.append(row)
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Mother", "Food"],
            "rows": rows
        }
    }
    
    # Print final JSON output
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")