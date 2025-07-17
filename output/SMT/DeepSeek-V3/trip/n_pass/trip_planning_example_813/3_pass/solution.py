from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Seville', 'Vilnius', 'Santorini', 'London', 'Stuttgart', 'Dublin', 'Frankfurt']
    city_map = {city: idx for idx, city in enumerate(cities)}
    n_days = 17

    # Direct flights
    direct_flights = {
        ('Frankfurt', 'Dublin'),
        ('Frankfurt', 'London'),
        ('London', 'Dublin'),
        ('Vilnius', 'Frankfurt'),
        ('Frankfurt', 'Stuttgart'),
        ('Dublin', 'Seville'),
        ('London', 'Santorini'),
        ('Stuttgart', 'London'),
        ('Santorini', 'Dublin')
    }

    # Create bidirectional flights
    bidirectional_flights = set()
    for a, b in direct_flights:
        bidirectional_flights.add((a, b))
        bidirectional_flights.add((b, a))
    direct_flights = bidirectional_flights

    # Z3 solver
    solver = Solver()

    # Variables: itinerary[day] = city index
    itinerary = [Int(f'day_{i}') for i in range(1, n_days + 1)]

    # Constraints: each day is a city index (0 to 6)
    for day in itinerary:
        solver.add(day >= 0, day < len(cities))

    # City day counts
    seville_days = sum([If(itinerary[i] == city_map['Seville'], 1, 0) for i in range(n_days)])
    vilnius_days = sum([If(itinerary[i] == city_map['Vilnius'], 1, 0) for i in range(n_days)])
    santorini_days = sum([If(itinerary[i] == city_map['Santorini'], 1, 0) for i in range(n_days)])
    london_days = sum([If(itinerary[i] == city_map['London'], 1, 0) for i in range(n_days)])
    stuttgart_days = sum([If(itinerary[i] == city_map['Stuttgart'], 1, 0) for i in range(n_days)])
    dublin_days = sum([If(itinerary[i] == city_map['Dublin'], 1, 0) for i in range(n_days)])
    frankfurt_days = sum([If(itinerary[i] == city_map['Frankfurt'], 1, 0) for i in range(n_days)])

    solver.add(seville_days == 5)
    solver.add(vilnius_days == 3)
    solver.add(santorini_days == 2)
    solver.add(london_days == 2)
    solver.add(stuttgart_days == 3)
    solver.add(dublin_days == 3)
    solver.add(frankfurt_days == 5)

    # London on days 9 and 10 (0-based: days 8 and 9)
    solver.add(itinerary[8] == city_map['London'])  # day 9
    solver.add(itinerary[9] == city_map['London'])  # day 10

    # Stuttgart on days 7 and 8 (0-based: days 6 and 7)
    solver.add(itinerary[6] == city_map['Stuttgart'])  # day 7
    solver.add(itinerary[7] == city_map['Stuttgart'])  # day 8

    # Flight constraints: consecutive days must be same city or have a direct flight
    for i in range(n_days - 1):
        current_city = itinerary[i]
        next_city = itinerary[i + 1]
        # Either same city or direct flight
        solver.add(Or(
            current_city == next_city,
            *[
                And(current_city == city_map[a], next_city == city_map[b])
                for a, b in direct_flights
            ]
        ))

    # Check if satisfiable
    if solver.check() == sat:
        model = solver.model()
        itinerary_result = []
        for i in range(n_days):
            day = i + 1
            city_idx = model.evaluate(itinerary[i]).as_long()
            city = cities[city_idx]
            itinerary_result.append({"day": day, "place": city})
        return {'itinerary': itinerary_result}
    else:
        return {'error': 'No valid itinerary found that satisfies all constraints.'}

# Solve and print the result
result = solve_itinerary()
print(json.dumps(result, indent=2))