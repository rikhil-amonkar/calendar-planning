from z3 import *
import json

# Define cities
cities = ['Warsaw', 'Budapest', 'Paris', 'Riga']
City = EnumSort('City', cities)
warsaw, budapest, paris, riga = [Const(c, City) for c in cities]
city_names = {warsaw: 'Warsaw', budapest: 'Budapest', paris: 'Paris', riga: 'Riga'}

# Direct flights (bidirectional)
direct_flights = [
    (warsaw, budapest),
    (warsaw, paris),
    (warsaw, riga),
    (budapest, paris),
    (paris, riga)
]

s = Solver()

# Create variables for each day (1-17)
stay_city = [Const(f'stay_city_{i}', City) for i in range(17)]
is_travel_day = [Bool(f'travel_{i}') for i in range(17)]
travel_from = [Const(f'travel_from_{i}', City) for i in range(17)]
travel_to = [Const(f'travel_to_{i}', City) for i in range(17)]

# Constraints for each day
for i in range(17):
    # If not travel day, stay_city must be one of the cities
    s.add(Implies(Not(is_travel_day[i]), 
                Or(stay_city[i] == warsaw, stay_city[i] == budapest, 
                   stay_city[i] == paris, stay_city[i] == riga))
    
    # If travel day, must have valid flight connection
    s.add(Implies(is_travel_day[i], 
                  Or([And(travel_from[i] == a, travel_to[i] == b) for a, b in direct_flights] + 
                     [And(travel_from[i] == b, travel_to[i] == a) for a, b in direct_flights])))
    
    # Travel endpoints must be different cities
    s.add(Implies(is_travel_day[i], travel_from[i] != travel_to[i]))

# Consistency between days
for i in range(16):
    # Next day's starting city must match current day's ending city
    s.add(If(is_travel_day[i], 
             travel_to[i] == If(is_travel_day[i+1], travel_from[i+1], stay_city[i+1]),
             stay_city[i] == If(is_travel_day[i+1], travel_from[i+1], stay_city[i+1])))

# Fixed constraints for days 1-2 (must be in Warsaw with no travel)
s.add(stay_city[0] == warsaw, Not(is_travel_day[0]))  # Day 1
s.add(stay_city[1] == warsaw, Not(is_travel_day[1]))  # Day 2

# Total days per city (considering both stay and travel)
warsaw_days = Int('warsaw_days')
budapest_days = Int('budapest_days')
paris_days = Int('paris_days')
riga_days = Int('riga_days')

s.add(warsaw_days == 2, budapest_days == 7, paris_days == 4, riga_days == 7)

# Count days in each city
warsaw_count = 0
budapest_count = 0
paris_count = 0
riga_count = 0

for i in range(17):
    # Stay days count fully
    warsaw_count += If(And(Not(is_travel_day[i]), stay_city[i] == warsaw, 1, 0)
    budapest_count += If(And(Not(is_travel_day[i]), stay_city[i] == budapest, 1, 0)
    paris_count += If(And(Not(is_travel_day[i]), stay_city[i] == paris, 1, 0)
    riga_count += If(And(Not(is_travel_day[i]), stay_city[i] == riga, 1, 0)
    
    # Travel days count half for departure and arrival
    warsaw_count += If(And(is_travel_day[i]), travel_from[i] == warsaw, 0.5, 0)
    warsaw_count += If(And(is_travel_day[i]), travel_to[i] == warsaw, 0.5, 0)
    
    budapest_count += If(And(is_travel_day[i]), travel_from[i] == budapest, 0.5, 0)
    budapest_count += If(And(is_travel_day[i]), travel_to[i] == budapest, 0.5, 0)
    
    paris_count += If(And(is_travel_day[i]), travel_from[i] == paris, 0.5, 0)
    paris_count += If(And(is_travel_day[i]), travel_to[i] == paris, 0.5, 0)
    
    riga_count += If(And(is_travel_day[i]), travel_from[i] == riga, 0.5, 0)
    riga_count += If(And(is_travel_day[i]), travel_to[i] == riga, 0.5, 0)

s.add(warsaw_days == warsaw_count, 
      budapest_days == budapest_count,
      paris_days == paris_count,
      riga_days == riga_count)

# Wedding in Riga between days 11-17 (inclusive)
wedding_constraint = Or([Or(
    And(Not(is_travel_day[i]), stay_city[i] == riga),
    And(is_travel_day[i], Or(travel_from[i] == riga, travel_to[i] == riga))
) for i in range(10, 17)])  # Days 11-17 (0-indexed 10-16)
s.add(wedding_constraint)

# Solve and format itinerary
if s.check() == sat:
    model = s.model()
    itinerary = []
    current_place = None
    start_day = 1
    current_day = 1
    
    # Helper to get day description
    def get_day_desc(i):
        if model[is_travel_day[i]]:
            from_city = city_names[model[travel_from[i]]]
            to_city = city_names[model[travel_to[i]]]
            return f"{from_city}-{to_city}"
        else:
            return city_names[model[stay_city[i]]]
    
    # Build itinerary by grouping consecutive days
    current_desc = get_day_desc(0)
    for i in range(1, 17):
        day_desc = get_day_desc(i)
        if day_desc == current_desc:
            current_day += 1
        else:
            itinerary.append({
                'day_range': f"Day {start_day}-{start_day + current_day - 1}",
                'place': current_desc
            })
            start_day += current_day
            current_day = 1
            current_desc = day_desc
    
    # Add last segment
    itinerary.append({
        'day_range': f"Day {start_day}-17",
        'place': current_desc
    })
    
    print(json.dumps({'itinerary': itinerary}, indent=2))
else:
    print("No solution found")