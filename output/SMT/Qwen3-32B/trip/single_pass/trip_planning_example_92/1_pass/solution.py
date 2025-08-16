from z3 import *
import json

# Define city codes
RIGA = 0
VILNIUS = 1
DUBLIN = 2

# Allowed direct flights
allowed_flights = [(RIGA, VILNIUS), (RIGA, DUBLIN), (DUBLIN, RIGA)]

# Create variables for each day (12 days total)
cities = [Int(f'day_{i}') for i in range(12)]

solver = Solver()

# Constraint: each day must be one of the three cities
for day in cities:
    solver.add(And(day >= RIGA, day <= DUBLIN))

# Constraints for consecutive days: transitions must be allowed flights or same city
for i in range(11):  # i from 0 to 10 (11 transitions)
    same_city = cities[i] == cities[i+1]
    allowed_transitions = Or([And(cities[i] == a, cities[i+1] == b) for (a, b) in allowed_flights])
    solver.add(Or(same_city, allowed_transitions))

# Calculate count for each city in the itinerary
count_riga = Sum([If(cities[i] == RIGA, 1, 0) for i in range(12)])
count_vilnius = Sum([If(cities[i] == VILNIUS, 1, 0) for i in range(12)])
count_dublin = Sum([If(cities[i] == DUBLIN, 1, 0) for i in range(12)])

# Calculate number of flights departing from each city
num_flights_from_riga = Sum([If(And(cities[i] == RIGA, cities[i+1] != RIGA), 1, 0) for i in range(11)])
num_flights_from_vilnius = Sum([If(And(cities[i] == VILNIUS, cities[i+1] != VILNIUS), 1, 0) for i in range(11)])
num_flights_from_dublin = Sum([If(And(cities[i] == DUBLIN, cities[i+1] != DUBLIN), 1, 0) for i in range(11)])

# Add constraints for total days in each city
solver.add(count_riga + num_flights_from_riga == 5)
solver.add(count_vilnius + num_flights_from_vilnius == 7)
solver.add(count_dublin + num_flights_from_dublin == 2)

# Check if the solver can find a solution
if solver.check() == sat:
    model = solver.model()
    itinerary = []
    for i in range(12):
        city_code = model.evaluate(cities[i])
        city_name = ''
        if city_code == RIGA:
            city_name = 'Riga'
        elif city_code == VILNIUS:
            city_name = 'Vilnius'
        elif city_code == DUBLIN:
            city_name = 'Dublin'
        else:
            city_name = 'Unknown'
        itinerary.append({'day': i + 1, 'city': city_name})
    print(json.dumps({'itinerary': itinerary}, indent=2))
else:
    print("No solution found.")