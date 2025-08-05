from z3 import *
import json

# Define city enumeration
City, (warsaw, budapest, paris, riga) = EnumSort('City', ['Warsaw', 'Budapest', 'Paris', 'Riga'])
city_names = {
    warsaw: "Warsaw",
    budapest: "Budapest",
    paris: "Paris",
    riga: "Riga"
}

# Define direct flight connections (both directions)
direct_flights = [
    (warsaw, budapest),
    (warsaw, riga),
    (budapest, paris),
    (warsaw, paris),
    (paris, riga)
]

# Initialize solver
s = Solver()

# Create start and end city variables for each day (17 days)
start_city = [Const(f'start_{i}', City) for i in range(1, 18)]
end_city = [Const(f'end_{i}', City) for i in range(1, 18)]

# Constraint: Start in Warsaw on day 1
s.add(start_city[0] == warsaw)

# Constraint: End city of day i is start city of day i+1
for i in range(16):
    s.add(end_city[i] == start_city[i+1])

# Must be in Warsaw on both day 1 and day 2
s.add(Or(start_city[0] == warsaw, end_city[0] == warsaw))  # Day 1
s.add(Or(start_city[1] == warsaw, end_city[1] == warsaw))  # Day 2

# Flight connectivity constraint
for i in range(17):
    # Only allow direct flights when cities change
    flight_taken = (start_city[i] != end_city[i])
    valid_flight = Or([Or(
        And(start_city[i] == a, end_city[i] == b),
        And(start_city[i] == b, end_city[i] == a)
    ) for (a, b) in direct_flights])
    s.add(Implies(flight_taken, valid_flight))

# Count days per city (including flight days)
def days_in_city(city):
    return Sum([If(Or(start_city[i] == city, end_city[i] == city), 1, 0) for i in range(17)])

s.add(days_in_city(riga) == 7)
s.add(days_in_city(budapest) == 7)
s.add(days_in_city(paris) == 4)
s.add(days_in_city(warsaw) == 2)

# Wedding in Riga between days 11-17 (inclusive)
wedding_constraint = Or([Or(start_city[i] == riga, end_city[i] == riga) for i in range(10, 17)])
s.add(wedding_constraint)

# Solve the constraints
if s.check() == sat:
    model = s.model()
    # Get place representation for each day
    daily_places = []
    for i in range(17):
        start_val = model.eval(start_city[i])
        end_val = model.eval(end_city[i])
        start_name = city_names[start_val]
        end_name = city_names[end_val]
        if start_name == end_name:
            place_str = start_name
        else:
            # Sort city names alphabetically for consistency
            cities = sorted([start_name, end_name])
            place_str = f"{cities[0]}-{cities[1]}"
        daily_places.append(place_str)
    
    # Group consecutive days with same place string
    itinerary = []
    start_day = 1
    current_place = daily_places[0]
    
    for day in range(2, 18):  # day from 2 to 17
        if daily_places[day-1] == current_place:
            continue
        else:
            end_day = day - 1
            itinerary.append({
                'day_range': f"Day {start_day}-{end_day}",
                'place': current_place
            })
            start_day = day
            current_place = daily_places[day-1]
    
    # Add the last segment
    itinerary.append({
        'day_range': f"Day {start_day}-17",
        'place': current_place
    })
    
    result = {'itinerary': itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")