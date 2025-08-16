from z3 import *
import json

s = Solver()

# Create integer variables (each between 1 and 4) representing the house number (1 = leftmost)
# for each person, car, birthday, and hobby.
pos_alice, pos_peter, pos_eric, pos_arnold = Ints('pos_alice pos_peter pos_eric pos_arnold')
pos_honda, pos_tesla, pos_toyota, pos_ford = Ints('pos_honda pos_tesla pos_toyota pos_ford')
pos_jan, pos_april, pos_sept, pos_feb = Ints('pos_jan pos_april pos_sept pos_feb')
pos_photo, pos_painting, pos_cooking, pos_gardening = Ints('pos_photo pos_painting pos_cooking pos_gardening')

# All variables must be between 1 and 4.
all_vars = [pos_alice, pos_peter, pos_eric, pos_arnold,
            pos_honda, pos_tesla, pos_toyota, pos_ford,
            pos_jan, pos_april, pos_sept, pos_feb,
            pos_photo, pos_painting, pos_cooking, pos_gardening]
for v in all_vars:
    s.add(And(v >= 1, v <= 4))

# In each category the four values must be all different.
s.add(Distinct(pos_alice, pos_peter, pos_eric, pos_arnold))
s.add(Distinct(pos_honda, pos_tesla, pos_toyota, pos_ford))
s.add(Distinct(pos_jan, pos_april, pos_sept, pos_feb))
s.add(Distinct(pos_photo, pos_painting, pos_cooking, pos_gardening))

# Now add the clues as constraints:

# 1. The person whose birthday is in January is not in the second house.
s.add(pos_jan != 2)

# 2. The photography enthusiast is somewhere to the left of Eric.
s.add(pos_photo < pos_eric)

# 3. The photography enthusiast is somewhere to the left of Peter.
s.add(pos_photo < pos_peter)

# 4. The person who owns a Honda Civic is directly left of the person who owns a Tesla Model 3.
s.add(pos_honda + 1 == pos_tesla)

# 5. There is one house between the person who owns a Tesla Model 3 and the person who enjoys gardening.
s.add(Or(pos_tesla + 2 == pos_gardening, pos_tesla - 2 == pos_gardening))

# 6. The person who owns a Tesla Model 3 is Arnold.
s.add(pos_tesla == pos_arnold)

# 7. The person whose birthday is in February is the person who loves cooking.
s.add(pos_feb == pos_cooking)

# 8. The person who owns a Toyota Camry is Peter.
s.add(pos_toyota == pos_peter)

# 9. The person whose birthday is in April is Arnold.
s.add(pos_april == pos_arnold)

# 10. Alice is the photography enthusiast.
s.add(pos_alice == pos_photo)

# 11. Peter is the person whose birthday is in January.
s.add(pos_peter == pos_jan)

# Solve the puzzle.
if s.check() == sat:
    m = s.model()
    
    # We'll build a mapping from house number to the attribute that ends up in that house.
    # For Names:
    names = {}
    names[m[pos_alice].as_long()] = "Alice"
    names[m[pos_peter].as_long()] = "Peter"
    names[m[pos_eric].as_long()] = "Eric"
    names[m[pos_arnold].as_long()] = "Arnold"
    
    # For Car Models:
    cars = {}
    cars[m[pos_honda].as_long()] = "honda civic"
    cars[m[pos_tesla].as_long()] = "tesla model 3"
    cars[m[pos_toyota].as_long()] = "toyota camry"
    cars[m[pos_ford].as_long()] = "ford f150"
    
    # For Birthdays:
    birthdays = {}
    birthdays[m[pos_jan].as_long()] = "jan"
    birthdays[m[pos_april].as_long()] = "april"
    birthdays[m[pos_sept].as_long()] = "sept"
    birthdays[m[pos_feb].as_long()] = "feb"
    
    # For Hobbies:
    hobbies = {}
    hobbies[m[pos_photo].as_long()] = "photography"
    hobbies[m[pos_painting].as_long()] = "painting"
    hobbies[m[pos_cooking].as_long()] = "cooking"
    hobbies[m[pos_gardening].as_long()] = "gardening"
    
    # Build the solution rows in order of houses 1 to 4.
    solution_rows = []
    for house in range(1, 5):
        row = [str(house),
               names.get(house, ""),
               cars.get(house, ""),
               birthdays.get(house, ""),
               hobbies.get(house, "")]
        solution_rows.append(row)
    
    solution = {
        "solution": {
            "header": ["House", "Name", "CarModel", "Birthday", "Hobby"],
            "rows": solution_rows
        }
    }
    print(json.dumps(solution, indent=2))
else:
    print("No solution found")