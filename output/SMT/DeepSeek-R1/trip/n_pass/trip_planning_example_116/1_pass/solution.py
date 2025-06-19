from z3 import *
import json

# Define the City datatype
City = Datatype('City')
City.declare('Split')
City.declare('Santorini')
City.declare('London')
City = City.create()

# Create solver
s = Solver()

# Define variables
f1 = Int('f1')
f2 = Int('f2')
city1 = Const('city1', City)
city2 = Const('city2', City)
city3 = Const('city3', City)

# Constraints for flight days
s.add(f1 >= 1, f1 <= 17)
s.add(f2 > f1, f2 <= 18)

# Cities must be distinct
s.add(Distinct(city1, city2, city3))

# Flight constraints: only direct flights allowed
s.add(Or(
    And(city1 == City.Split, city2 == City.London),
    And(city1 == City.London, city2 == City.Split),
    And(city1 == City.London, city2 == City.Santorini),
    And(city1 == City.Santorini, city2 == City.London)
))

s.add(Or(
    And(city2 == City.Split, city3 == City.London),
    And(city2 == City.London, city3 == City.Split),
    And(city2 == City.London, city3 == City.Santorini),
    And(city2 == City.Santorini, city3 == City.London)
))

# Must be in Santorini on day 18 -> last stay is Santorini
s.add(city3 == City.Santorini)

# Must be in Santorini on day 12 -> the last stay must include day 12
s.add(f2 <= 12)

# Total days per city
split_days = If(city1 == City.Split, f1, 0) + \
             If(city2 == City.Split, (f2 - f1 + 1), 0) + \
             If(city3 == City.Split, (18 - f2 + 1), 0)
s.add(split_days == 6)

london_days = If(city1 == City.London, f1, 0) + \
              If(city2 == City.London, (f2 - f1 + 1), 0) + \
              If(city3 == City.London, (18 - f2 + 1), 0)
s.add(london_days == 7)

santorini_days = If(city1 == City.Santorini, f1, 0) + \
                 If(city2 == City.Santorini, (f2 - f1 + 1), 0) + \
                 If(city3 == City.Santorini, (18 - f2 + 1), 0)
s.add(santorini_days == 7)

# Solve the constraints
if s.check() == sat:
    m = s.model()
    f1_val = m[f1].as_long()
    f2_val = m[f2].as_long()
    city1_val = m[city1]
    city2_val = m[city2]
    city3_val = m[city3]
    
    # Helper function to convert City to string
    def city_to_str(city_val):
        if city_val == City.Split:
            return "Split"
        elif city_val == City.Santorini:
            return "Santorini"
        elif city_val == City.London:
            return "London"
    
    city1_str = city_to_str(city1_val)
    city2_str = city_to_str(city2_val)
    city3_str = city_to_str(city3_val)
    
    # Build itinerary
    itinerary = [
        {"day_range": f"Day 1-{f1_val}", "place": city1_str},
        {"day_range": f"Day {f1_val}", "place": city1_str},
        {"day_range": f"Day {f1_val}", "place": city2_str},
        {"day_range": f"Day {f1_val}-{f2_val}", "place": city2_str},
        {"day_range": f"Day {f2_val}", "place": city2_str},
        {"day_range": f"Day {f2_val}", "place": city3_str},
        {"day_range": f"Day {f2_val}-18", "place": city3_str}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))
else:
    print('{"error": "No solution found"}')