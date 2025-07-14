from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Prague', 'Lyon', 'Frankfurt', 'Helsinki', 'Naples']
    city_map = {city: idx for idx, city in enumerate(cities)}
    n_cities = len(cities)
    n_days = 12

    # Direct flights: adjacency list
    direct_flights = {
        'Prague': ['Lyon', 'Frankfurt', 'Helsinki'],
        'Lyon': ['Prague', 'Frankfurt'],
        'Frankfurt': ['Prague', 'Lyon', 'Helsinki', 'Naples'],
        'Helsinki': ['Prague', 'Frankfurt', 'Naples'],
        'Naples': ['Helsinki', 'Frankfurt']
    }

    # Z3 variables: day i is in city c
    X = [[Bool(f"day_{i+1}_city_{c}") for c in range(n_cities)] for i in range(n_days)]

    s = Solver()

    # Each day is in exactly one city
    for i in range(n_days):
        s.add(Or([X[i][c] for c in range(n_cities)]))
        for c1 in range(n_cities):
            for c2 in range(c1 + 1, n_cities):
                s.add(Or(Not(X[i][c1]), Not(X[i][c2])))

    # Flight constraints: consecutive days must be in the same city or connected by direct flight
    for i in range(n_days - 1):
        current_possible = []
        for c1 in range(n_cities):
            for c2 in range(n_cities):
                if c1 == c2:
                    current_possible.append(And(X[i][c1], X[i+1][c2]))
                else:
                    city1 = cities[c1]
                    city2 = cities[c2]
                    if city2 in direct_flights.get(city1, []):
                        current_possible.append(And(X[i][c1], X[i+1][c2]))
        s.add(Or(current_possible))

    # Day constraints
    # Prague: 2 days, including day 1 or 2 (workshop between day 1 and 2)
    prague_days = []
    for i in range(n_days):
        prague_days.append(X[i][city_map['Prague']])
    s.add(Sum([If(c, 1, 0) for c in prague_days]) == 2)
    # The workshop is between day 1 and 2, so at least one of day 1 or 2 is in Prague
    s.add(Or(X[0][city_map['Prague']], X[1][city_map['Prague']]))

    # Helsinki: 4 days, including days 2-5 (annual show)
    helsinki_days = []
    for i in range(n_days):
        helsinki_days.append(X[i][city_map['Helsinki']])
    s.add(Sum([If(c, 1, 0) for c in helsinki_days]) == 4)
    # Days 2-5 (indices 1-4) must include Helsinki
    for i in range(1, 5):  # days 2 to 5 (1-based to 0-based)
        s.add(X[i][city_map['Helsinki']])

    # Frankfurt: 3 days
    frankfurt_days = []
    for i in range(n_days):
        frankfurt_days.append(X[i][city_map['Frankfurt']])
    s.add(Sum([If(c, 1, 0) for c in frankfurt_days]) == 3)

    # Lyon: 3 days
    lyon_days = []
    for i in range(n_days):
        lyon_days.append(X[i][city_map['Lyon']])
    s.add(Sum([If(c, 1, 0) for c in lyon_days]) == 3)

    # Naples: 4 days
    naples_days = []
    for i in range(n_days):
        naples_days.append(X[i][city_map['Naples']])
    s.add(Sum([If(c, 1, 0) for c in naples_days]) == 4)

    # Check and get model
    if s.check() == sat:
        m = s.model()
        day_assignments = []
        for i in range(n_days):
            for c in range(n_cities):
                if m.evaluate(X[i][c]):
                    day_assignments.append(cities[c])
                    break

        # Generate itinerary with day ranges and flight days
        itinerary = []
        current_place = day_assignments[0]
        start_day = 1

        for i in range(1, n_days + 1):
            if i == n_days or day_assignments[i] != current_place:
                end_day = i
                if start_day == end_day:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": current_place})
                if i < n_days:
                    # Flight day: add both departure and arrival
                    itinerary.append({"day_range": f"Day {i+1}", "place": current_place})
                    itinerary.append({"day_range": f"Day {i+1}", "place": day_assignments[i]})
                    current_place = day_assignments[i]
                    start_day = i + 1
            # else continue

        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Solve and print the itinerary
itinerary = solve_itinerary()
import json
print(json.dumps(itinerary, indent=2))