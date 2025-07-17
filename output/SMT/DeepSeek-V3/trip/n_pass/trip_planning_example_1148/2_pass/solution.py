from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Lisbon', 'Dubrovnik', 'Copenhagen', 'Prague', 'Tallinn', 'Stockholm', 'Split', 'Lyon']
    # Direct flights as tuples (from, to)
    direct_flights = [
        ('Dubrovnik', 'Stockholm'), ('Lisbon', 'Copenhagen'), ('Lisbon', 'Lyon'), 
        ('Copenhagen', 'Stockholm'), ('Copenhagen', 'Split'), ('Prague', 'Stockholm'), 
        ('Tallinn', 'Stockholm'), ('Prague', 'Lyon'), ('Lisbon', 'Stockholm'), 
        ('Prague', 'Lisbon'), ('Stockholm', 'Split'), ('Prague', 'Copenhagen'), 
        ('Split', 'Lyon'), ('Copenhagen', 'Dubrovnik'), ('Prague', 'Split'), 
        ('Tallinn', 'Copenhagen'), ('Tallinn', 'Prague')
    ]
    # Make flights bidirectional
    bidirectional_flights = set()
    for (a, b) in direct_flights:
        bidirectional_flights.add((a, b))
        bidirectional_flights.add((b, a))
    # Number of days
    days = 19
    # Create a Z3 solver
    solver = Solver()
    # Variables: day[i] is the city on day i+1 (since days are 1-based)
    day = [Int(f'day_{i}') for i in range(days)]
    # Each day variable must be an index representing a city (0 to 7)
    city_map = {i: city for i, city in enumerate(cities)}
    city_rev = {city: i for i, city in enumerate(cities)}
    for d in day:
        solver.add(d >= 0, d < len(cities))
    # Constraints for transitions: consecutive days must be same city or connected by direct flight
    for i in range(days - 1):
        current_city = day[i]
        next_city = day[i + 1]
        # Either stay in the same city or move to a connected city
        solver.add(Or(
            current_city == next_city,
            *[And(current_city == city_rev[a], next_city == city_rev[b]) 
              for (a, b) in bidirectional_flights]
        ))
    # Duration constraints
    # Lisbon: 2 days total (including transition days)
    solver.add(Sum([If(day[i] == city_rev['Lisbon'], 1, 0) for i in range(days)]) == 2)
    # Workshop in Lisbon between day 4 and 5 (so day 4 or 5 must be in Lisbon)
    solver.add(Or(day[3] == city_rev['Lisbon'], day[4] == city_rev['Lisbon']))
    # Dubrovnik: 5 days
    solver.add(Sum([If(day[i] == city_rev['Dubrovnik'], 1, 0) for i in range(days)]) == 5)
    # Copenhagen: 5 days
    solver.add(Sum([If(day[i] == city_rev['Copenhagen'], 1, 0) for i in range(days)]) == 5)
    # Prague: 3 days
    solver.add(Sum([If(day[i] == city_rev['Prague'], 1, 0) for i in range(days)]) == 3)
    # Tallinn: 2 days
    solver.add(Sum([If(day[i] == city_rev['Tallinn'], 1, 0) for i in range(days)]) == 2)
    # Meet friend in Tallinn between day 1 and 2 (so day 0 or 1 must be Tallinn)
    solver.add(Or(day[0] == city_rev['Tallinn'], day[1] == city_rev['Tallinn']))
    # Stockholm: 4 days
    solver.add(Sum([If(day[i] == city_rev['Stockholm'], 1, 0) for i in range(days)]) == 4)
    # Wedding in Stockholm between day 13 and 16 (so days 12,13,14, or 15 must be Stockholm (0-based))
    solver.add(Or([day[i] == city_rev['Stockholm'] for i in range(12, 16)]))
    # Split: 3 days
    solver.add(Sum([If(day[i] == city_rev['Split'], 1, 0) for i in range(days)]) == 3)
    # Lyon: 2 days
    solver.add(Sum([If(day[i] == city_rev['Lyon'], 1, 0) for i in range(days)]) == 2)
    # Annual show in Lyon from day 18 to 19 (0-based days 17 and 18 must be Lyon)
    solver.add(day[17] == city_rev['Lyon'])
    solver.add(day[18] == city_rev['Lyon'])
    # Check if the solver can find a solution
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(days):
            city_index = model.evaluate(day[i]).as_long()
            itinerary.append({"day": i + 1, "place": cities[city_index]})
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print the result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))