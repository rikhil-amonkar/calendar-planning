from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Valencia', 'Oslo', 'Lyon', 'Prague', 'Paris', 'Nice', 'Seville', 'Tallinn', 'Mykonos', 'Lisbon']
    city_map = {city: i for i, city in enumerate(cities)}
    num_cities = len(cities)
    num_days = 25

    # Direct flights
    direct_flights = {
        'Lisbon': ['Paris', 'Seville', 'Prague', 'Valencia', 'Nice', 'Oslo', 'Lyon'],
        'Lyon': ['Nice', 'Prague', 'Paris', 'Valencia', 'Oslo'],
        'Nice': ['Lyon', 'Oslo', 'Paris', 'Mykonos', 'Lisbon'],
        'Oslo': ['Tallinn', 'Paris', 'Nice', 'Prague', 'Lyon'],
        'Paris': ['Lisbon', 'Oslo', 'Valencia', 'Nice', 'Lyon', 'Tallinn', 'Prague', 'Seville'],
        'Prague': ['Lyon', 'Lisbon', 'Oslo', 'Paris', 'Tallinn', 'Valencia'],
        'Seville': ['Lisbon', 'Paris', 'Valencia'],
        'Tallinn': ['Oslo', 'Paris', 'Prague'],
        'Mykonos': ['Nice'],
        'Valencia': ['Paris', 'Lisbon', 'Lyon', 'Seville', 'Prague']
    }

    # Z3 variables: day[i] is the city on day i (0-based)
    day = [Int(f'day_{i}') for i in range(num_days)]
    s = Solver()

    # Each day must be one of the cities
    for d in day:
        s.add(And(d >= 0, d < num_cities))

    # Duration constraints
    # Valencia: 2 days, including day 3 or 4 (1-based, so days 2 or 3 in 0-based)
    valencia_days = [If(day[i] == city_map['Valencia'], 1, 0) for i in range(num_days)]
    s.add(sum(valencia_days) == 2)
    s.add(Or(day[2] == city_map['Valencia'], day[3] == city_map['Valencia']))

    # Oslo: 3 days, including day 13-15 (0-based 12-14)
    oslo_days = [If(day[i] == city_map['Oslo'], 1, 0) for i in range(num_days)]
    s.add(sum(oslo_days) == 3)
    s.add(Or([day[i] == city_map['Oslo'] for i in range(12, 15)]))

    # Lyon: 4 days
    lyon_days = [If(day[i] == city_map['Lyon'], 1, 0) for i in range(num_days)]
    s.add(sum(lyon_days) == 4)

    # Prague: 3 days
    prague_days = [If(day[i] == city_map['Prague'], 1, 0) for i in range(num_days)]
    s.add(sum(prague_days) == 3)

    # Paris: 4 days
    paris_days = [If(day[i] == city_map['Paris'], 1, 0) for i in range(num_days)]
    s.add(sum(paris_days) == 4)

    # Nice: 4 days
    nice_days = [If(day[i] == city_map['Nice'], 1, 0) for i in range(num_days)]
    s.add(sum(nice_days) == 4)

    # Seville: 5 days, including days 5-9 (0-based 4-8)
    seville_days = [If(day[i] == city_map['Seville'], 1, 0) for i in range(num_days)]
    s.add(sum(seville_days) == 5)
    for i in range(4, 9):
        s.add(day[i] == city_map['Seville'])

    # Tallinn: 2 days
    tallinn_days = [If(day[i] == city_map['Tallinn'], 1, 0) for i in range(num_days)]
    s.add(sum(tallinn_days) == 2)

    # Mykonos: 5 days, including days 21-25 (0-based 20-24)
    mykonos_days = [If(day[i] == city_map['Mykonos'], 1, 0) for i in range(num_days)]
    s.add(sum(mykonos_days) == 5)
    for i in range(20, 25):
        s.add(day[i] == city_map['Mykonos'])

    # Lisbon: 2 days
    lisbon_days = [If(day[i] == city_map['Lisbon'], 1, 0) for i in range(num_days)]
    s.add(sum(lisbon_days) == 2)

    # Flight constraints: consecutive days must be same city or have a direct flight
    for i in range(num_days - 1):
        current_city = day[i]
        next_city = day[i + 1]
        same_city = (current_city == next_city)
        flight_possible = Or([And(current_city == city_map[src], next_city == city_map[dst]) 
                            for src in direct_flights 
                            for dst in direct_flights[src]])
        s.add(Or(same_city, flight_possible))

    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(num_days):
            city_idx = m.evaluate(day[i]).as_long()
            itinerary.append({'day': i + 1, 'city': cities[city_idx]})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Generate and print the itinerary
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))