import json
from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Frankfurt', 'Manchester', 'Valencia', 'Naples', 'Oslo', 'Vilnius']
    city_map = {city: idx for idx, city in enumerate(cities)}
    idx_to_city = {idx: city for idx, city in enumerate(cities)}

    # Direct flights: adjacency list
    direct_flights = {
        'Valencia': ['Frankfurt', 'Naples'],
        'Manchester': ['Frankfurt', 'Naples', 'Oslo'],
        'Naples': ['Manchester', 'Frankfurt', 'Oslo', 'Valencia'],
        'Oslo': ['Naples', 'Frankfurt', 'Vilnius', 'Manchester'],
        'Vilnius': ['Frankfurt', 'Oslo'],
        'Frankfurt': ['Valencia', 'Manchester', 'Naples', 'Oslo', 'Vilnius']
    }

    # Days are 1..16
    days = 16
    Day = [i+1 for i in range(days)]

    # Z3 variables: day[i] is the city index for day i+1 (since days start at 1)
    city_vars = [Int(f'day_{i}') for i in range(days)]

    s = Solver()

    # Each day's city must be 0..5
    for d in range(days):
        s.add(And(city_vars[d] >= 0, city_vars[d] <= 5))

    # Fixed constraints:
    # Vilnius on day 12 and 13 (wedding)
    s.add(city_vars[11] == city_map['Vilnius'])
    s.add(city_vars[12] == city_map['Vilnius'])

    # Frankfurt from day 13 to 16 (days 13,14,15,16 are indices 12,13,14,15)
    for d in range(12, 16):
        s.add(city_vars[d] == city_map['Frankfurt'])

    # Flight transitions: consecutive days must be same city or connected by direct flight
    for d in range(days - 1):
        current_city = city_vars[d]
        next_city = city_vars[d+1]
        # Either same city or connected
        same_city = current_city == next_city
        connected = Or([And(current_city == city_map[c1], next_city == city_map[c2])
                      for c1 in direct_flights for c2 in direct_flights[c1]])
        s.add(Or(same_city, connected))

    # Duration constraints: total days in each city
    # Frankfurt: 4 days (days 13-16 are 4 days, so no additional days)
    frankfurt_days = sum([If(city_vars[d] == city_map['Frankfurt'], 1, 0) for d in range(days)])
    s.add(frankfurt_days == 4)

    # Manchester: 4 days
    manchester_days = sum([If(city_vars[d] == city_map['Manchester'], 1, 0) for d in range(days)])
    s.add(manchester_days == 4)

    # Valencia: 4 days
    valencia_days = sum([If(city_vars[d] == city_map['Valencia'], 1, 0) for d in range(days)])
    s.add(valencia_days == 4)

    # Naples: 4 days
    naples_days = sum([If(city_vars[d] == city_map['Naples'], 1, 0) for d in range(days)])
    s.add(naples_days == 4)

    # Oslo: 3 days
    oslo_days = sum([If(city_vars[d] == city_map['Oslo'], 1, 0) for d in range(days)])
    s.add(oslo_days == 3)

    # Vilnius: 2 days (days 12 and 13)
    vilnius_days = sum([If(city_vars[d] == city_map['Vilnius'], 1, 0) for d in range(days)])
    s.add(vilnius_days == 2)

    # Check if the solver can find a model
    if s.check() == sat:
        model = s.model()
        day_assignments = []
        for d in range(days):
            city_idx = model.evaluate(city_vars[d]).as_long()
            day_assignments.append(idx_to_city[city_idx])

        # Process day_assignments into the itinerary format
        itinerary = []
        current_place = day_assignments[0]
        start_day = 1
        for d in range(1, days):
            if day_assignments[d] != current_place:
                # Add the stay up to the previous day
                if start_day == d:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{d}", "place": current_place})
                # Add the flight day entries
                itinerary.append({"day_range": f"Day {d}", "place": current_place})
                itinerary.append({"day_range": f"Day {d}", "place": day_assignments[d]})
                current_place = day_assignments[d]
                start_day = d + 1
        # Add the last stay
        if start_day == days:
            itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
        else:
            itinerary.append({"day_range": f"Day {start_day}-{days}", "place": current_place})

        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))