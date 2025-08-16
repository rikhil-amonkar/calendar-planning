from z3 import *
import json

# Define cities: 0=Mykonos, 1=Vienna, 2=Venice
days = 10
cities = [Int(f'city_{i}') for i in range(days)]

s = Solver()

# Each day must be one of the three cities
for d in cities:
    s.add(Or(d == 0, d == 1, d == 2))

# Workshop constraint: Venice (2) on days 5-10 (indices 4-9)
for i in range(4, 10):
    s.add(cities[i] == 2)

# Count the number of days each city appears in the itinerary
def count_days_in_itinerary(city_code):
    return Sum([If(c == city_code, 1, 0) for c in cities])

# Count the number of flights involving the city
def count_flights_involving(city_code):
    flights = 0
    for i in range(days - 1):
        prev = cities[i]
        next_city = cities[i+1]
        is_flight = If(prev != next_city, 1, 0)
        involves_city = If(Or(prev == city_code, next_city == city_code), 1, 0)
        flights += is_flight * involves_city
    return flights

# Total days for each city
total_days_mykonos = count_days_in_itinerary(0) + count_flights_involving(0)
total_days_vienna = count_days_in_itinerary(1) + count_flights_involving(1)
total_days_venice = count_days_in_itinerary(2) + count_flights_involving(2)

# Add constraints for required days
s.add(total_days_mykonos == 2)
s.add(total_days_vienna == 4)
s.add(total_days_venice == 6)

# Check if the solver can find a solution
if s.check() == sat:
    model = s.model()
    itinerary = [model.evaluate(c).as_long() for c in cities]
    # Map to city names
    city_names = {0: 'Mykonos', 1: 'Vienna', 2: 'Venice'}
    result = [{'day': i+1, 'city': city_names[city]} for i, city in enumerate(itinerary)]
    output = {'itinerary': result}
    print(json.dumps(output, indent=2))
else:
    print("No solution found")