from z3 import *
import json

# Create solver instance
s = Solver()

# Define house positions: 1, 2, 3
houses = [1, 2, 3]

# Define variables for each category with domain 1..3
# Names
peter   = Int('peter')
arnold  = Int('arnold')
eric    = Int('eric')

# Car Models
toyota_camry   = Int('toyota_camry')
ford_f150      = Int('ford_f150')
tesla_model3   = Int('tesla_model3')

# House Styles
ranch     = Int('ranch')
colonial  = Int('colonial')
victorian = Int('victorian')

# Pets
cat  = Int('cat')
dog  = Int('dog')
fish = Int('fish')

# Occupations
engineer = Int('engineer')
doctor   = Int('doctor')
teacher  = Int('teacher')

# Vacation Preferences
city     = Int('city')
mountain = Int('mountain')
beach    = Int('beach')

# Domain constraints: Each variable must be in {1,2,3}
variables = [peter, arnold, eric,
             toyota_camry, ford_f150, tesla_model3,
             ranch, colonial, victorian,
             cat, dog, fish,
             engineer, doctor, teacher,
             city, mountain, beach]

for var in variables:
    s.add(And(var >= 1, var <= 3))

# All-different constraints for each category
s.add(Distinct(peter, arnold, eric))
s.add(Distinct(toyota_camry, ford_f150, tesla_model3))
s.add(Distinct(ranch, colonial, victorian))
s.add(Distinct(cat, dog, fish))
s.add(Distinct(engineer, doctor, teacher))
s.add(Distinct(city, mountain, beach))

# Puzzle clues:

# 1. The person with an aquarium of fish is in the first house.
s.add(fish == 1)

# 2. The person who owns a Toyota Camry is in the second house.
s.add(toyota_camry == 2)

# 3. The person who enjoys mountain retreats is not in the second house.
s.add(mountain != 2)

# 4. The person who prefers city breaks is not in the second house.
s.add(city != 2)

# 5. The person in a ranch-style home is somewhere to the left of Peter.
s.add(ranch < peter)

# 6. The person who owns a Toyota Camry is directly left of the person living in a colonial-style house.
s.add(toyota_camry + 1 == colonial)

# 7. Arnold is the person who has a cat.
s.add(arnold == cat)

# 8. Eric is somewhere to the left of the person who enjoys mountain retreats.
s.add(eric < mountain)

# 9. The person who is an engineer is not in the third house.
s.add(engineer != 3)

# 10. The person who owns a Tesla Model 3 is somewhere to the left of the person who is a teacher.
s.add(tesla_model3 < teacher)

# 11. The person who owns a dog is the person who is an engineer.
s.add(dog == engineer)

# Check for satisfiability
if s.check() == sat:
    m = s.model()
    
    # Create dictionaries mapping house number to attribute value
    house_to_name = {}
    house_to_car = {}
    house_to_style = {}
    house_to_pet = {}
    house_to_occ = {}
    house_to_vac = {}
    
    # Determine name for each house
    if m[peter] is not None:
        house_to_name[m[peter].as_long()] = "Peter"
    if m[arnold] is not None:
        house_to_name[m[arnold].as_long()] = "Arnold"
    if m[eric] is not None:
        house_to_name[m[eric].as_long()] = "Eric"
    
    # Determine car model for each house
    if m[toyota_camry] is not None:
        house_to_car[m[toyota_camry].as_long()] = "toyota camry"
    if m[ford_f150] is not None:
        house_to_car[m[ford_f150].as_long()] = "ford f150"
    if m[tesla_model3] is not None:
        house_to_car[m[tesla_model3].as_long()] = "tesla model 3"
    
    # Determine house style for each house
    if m[ranch] is not None:
        house_to_style[m[ranch].as_long()] = "ranch"
    if m[colonial] is not None:
        house_to_style[m[colonial].as_long()] = "colonial"
    if m[victorian] is not None:
        house_to_style[m[victorian].as_long()] = "victorian"
    
    # Determine pet for each house
    if m[cat] is not None:
        house_to_pet[m[cat].as_long()] = "cat"
    if m[dog] is not None:
        house_to_pet[m[dog].as_long()] = "dog"
    if m[fish] is not None:
        house_to_pet[m[fish].as_long()] = "fish"
    
    # Determine occupation for each house
    if m[engineer] is not None:
        house_to_occ[m[engineer].as_long()] = "engineer"
    if m[doctor] is not None:
        house_to_occ[m[doctor].as_long()] = "doctor"
    if m[teacher] is not None:
        house_to_occ[m[teacher].as_long()] = "teacher"
    
    # Determine vacation preference for each house
    if m[city] is not None:
        house_to_vac[m[city].as_long()] = "city"
    if m[mountain] is not None:
        house_to_vac[m[mountain].as_long()] = "mountain"
    if m[beach] is not None:
        house_to_vac[m[beach].as_long()] = "beach"
    
    # Build JSON output with houses in order 1, 2, 3
    rows = []
    for house in houses:
        row = [
            str(house),
            house_to_name.get(house, ""),
            house_to_car.get(house, ""),
            house_to_style.get(house, ""),
            house_to_pet.get(house, ""),
            house_to_occ.get(house, ""),
            house_to_vac.get(house, "")
        ]
        rows.append(row)
    
    result = {
        "solution": {
            "header": ["House", "Name", "CarModel", "HouseStyle", "Pet", "Occupation", "Vacation"],
            "rows": rows
        }
    }
    print(json.dumps(result))
else:
    print(json.dumps({"solution": {"header": ["House", "Name", "CarModel", "HouseStyle", "Pet", "Occupation", "Vacation"], "rows": []}}))