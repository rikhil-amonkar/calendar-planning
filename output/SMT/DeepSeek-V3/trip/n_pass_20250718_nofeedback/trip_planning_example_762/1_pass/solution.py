from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Dublin', 'Madrid', 'Oslo', 'London', 'Vilnius', 'Berlin']
    city_map = {city: idx for idx, city in enumerate(cities)}
    n_days = 13

    # Direct flights: list of tuples (city1, city2)
    direct_flights = [
        ('London', 'Madrid'),
        ('Oslo', 'Vilnius'),
        ('Berlin', 'Vilnius'),
        ('Madrid', 'Oslo'),
        ('Madrid', 'Dublin'),
        ('London', 'Oslo'),
        ('Madrid', 'Berlin'),
        ('Berlin', 'Oslo'),
        ('Dublin', 'Oslo'),
        ('London', 'Dublin'),
        ('London', 'Berlin'),
        ('Berlin', 'Dublin')
    ]
    # Correcting the typo in 'Madrid' in the direct_flights list
    corrected_flights = []
    for c1, c2 in direct_flights:
        if c1 == 'Madrid' or c2 == 'Madrid':
            corrected_flights.append((c1.replace('Madrid', 'Madrid'), c2.replace('Madrid', 'Madrid')))
        else:
            corrected_flights.append((c1, c2))
    direct_flights = corrected_flights

    # Create adjacency list for flight connections
    adjacency = {city: set() for city in cities}
    for c1, c2 in direct_flights:
        adjacency[c1].add(c2)
        adjacency[c2].add(c1)

    # Z3 variables: day[i] is the city visited on day i+1 (days 1..13)
    day = [Int(f"day_{i}") for i in range(n_days)]
    solver = Solver()

    # Each day's city must be one of the 6 cities
    for d in day:
        solver.add(Or([d == city_map[city] for city in cities]))

    # Constraints for days in each city
    # Dublin: 3 days, including days with friends between 7-9 (days 7-9 are indices 6-8)
    dublin_days = [If(day[i] == city_map['Dublin'], 1, 0) for i in range(n_days)]
    solver.add(sum(dublin_days) == 3)
    solver.add(Or([day[i] == city_map['Dublin'] for i in [6,7,8]]))

    # Madrid: 2 days, relatives between day 2-3 (indices 1-2)
    madrid_days = [If(day[i] == city_map['Madrid'], 1, 0) for i in range(n_days)]
    solver.add(sum(madrid_days) == 2)
    solver.add(Or(day[1] == city_map['Madrid'], day[2] == city_map['Madrid']))

    # Oslo: 3 days
    oslo_days = [If(day[i] == city_map['Oslo'], 1, 0) for i in range(n_days)]
    solver.add(sum(oslo_days) == 3)

    # London: 2 days
    london_days = [If(day[i] == city_map['London'], 1, 0) for i in range(n_days)]
    solver.add(sum(london_days) == 2)

    # Vilnius: 3 days
    vilnius_days = [If(day[i] == city_map['Vilnius'], 1, 0) for i in range(n_days)]
    solver.add(sum(vilnius_days) == 3)

    # Berlin: 5 days, wedding between day 3-7 (indices 2-6)
    berlin_days = [If(day[i] == city_map['Berlin'], 1, 0) for i in range(n_days)]
    solver.add(sum(berlin_days) == 5)
    solver.add(Or([day[i] == city_map['Berlin'] for i in range(2, 7)]))

    # Flight constraints: consecutive days in different cities must have a direct flight
    for i in range(n_days - 1):
        current_city = day[i]
        next_city = day[i+1]
        # If cities are different, check flight connection
        solver.add(Implies(current_city != next_city,
                          Or([And(current_city == city_map[c1], next_city == city_map[c2]) for c1, c2 in direct_flights] +
                             [And(current_city == city_map[c2], next_city == city_map[c1]) for c1, c2 in direct_flights])))

    # Check if the problem is satisfiable
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        city_names = {idx: city for city, idx in city_map.items()}
        for i in range(n_days):
            city_idx = model.eval(day[i]).as_long()
            itinerary.append({"day": i+1, "place": city_names[city_idx]})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print the result
import json
result = solve_itinerary()
print(json.dumps(result, indent=2))