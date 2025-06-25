from z3 import *
import json

# Define the cities and their corresponding flight durations
cities = ['Vilnius', 'Munich', 'Mykonos']
flight_durations = {
    ('Vilnius', 'Munich'): 1,
    ('Munich', 'Mykonos'): 1,
}

# Define the total number of days
total_days = 12

# Define the minimum stay in each city
min_stay = {
    'Vilnius': 4,
    'Munich': 3,
    'Mykonos': 7,
}

# Define the variables
days = [Int('day_' + str(i)) for i in range(total_days + 1)]
places = [Int('place_' + str(i)) for i in range(total_days + 1)]

# Define the constraints
solver = Solver()

# Initialize the first day
solver.add(And(days[0] == 1, places[0] == 0))

# Constraints for the minimum stay in each city
for city in cities:
    min_day = min_stay[city]
    for i in range(total_days + 1):
        if i >= min_day:
            solver.add(Or(And(days[i] == days[i - min_day] + 1, places[i] == cities.index(city))))
        else:
            solver.add(places[i]!= cities.index(city))

# Constraints for the flight durations
for (from_city, to_city), duration in flight_durations.items():
    from_index = cities.index(from_city)
    to_index = cities.index(to_city)
    for i in range(total_days + 1):
        if i + duration <= total_days:
            solver.add(Or(And(days[i + duration] == days[i] + 1, places[i + duration] == to_index)))
        else:
            solver.add(places[i] == to_index)

# Add a constraint to cover exactly 12 days
days_12 = [days[i] == i + 1 for i in range(total_days)]
solver.add(And(days_12))

# Find a solution
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    current_day = 1
    current_place = 0
    for i in range(total_days + 1):
        day = model[days[i]].as_long()
        place = model[places[i]].as_long()
        city = cities[place]
        if i > 0 and day!= model[days[i - 1]].as_long() + 1:
            itinerary.append({"day_range": f"Day {current_day}-{model[days[i - 1]].as_long() - 1}", "place": cities[current_place]})
            itinerary.append({"day_range": f"Day {model[days[i - 1]].as_long()}", "place": city})
            current_day = model[days[i - 1]].as_long()
            current_place = place
        elif i == 0:
            itinerary.append({"day_range": f"Day {day}", "place": city})
            current_day = day
            current_place = place
        else:
            itinerary.append({"day_range": f"Day {day}", "place": city})
            current_day = day
            current_place = place
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found")