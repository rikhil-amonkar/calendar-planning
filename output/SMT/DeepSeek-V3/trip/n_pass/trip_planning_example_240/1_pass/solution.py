from z3 import *
import json

def solve_itinerary():
    s = Solver()

    cities = ['Prague', 'Berlin', 'Tallinn', 'Stockholm']
    city_idx = {city: i for i, city in enumerate(cities)}
    n_days = 12

    # Direct flights adjacency list
    direct_flights = {
        'Berlin': ['Tallinn', 'Stockholm'],
        'Tallinn': ['Berlin', 'Prague', 'Stockholm'],
        'Prague': ['Tallinn', 'Stockholm'],
        'Stockholm': ['Tallinn', 'Prague', 'Berlin']
    }

    # presence[d][c] is True if the person is in city c on day d (1-based)
    presence = [[Bool(f"day_{day+1}_city_{city}") for city in cities] for day in range(n_days)]

    # Each day must be in at least one city
    for day in range(n_days):
        s.add(Or(presence[day]))

    # On a day, at most two cities can be present (flight day)
    for day in range(n_days):
        s.add(AtMost(*presence[day], 2))

    # If two cities are present on a day, they must have a direct flight
    for day in range(n_days):
        for c1 in range(len(cities)):
            for c2 in range(c1 + 1, len(cities)):
                city1 = cities[c1]
                city2 = cities[c2]
                s.add(Implies(And(presence[day][c1], presence[day][c2]), 
                             Or(city2 in direct_flights[city1], city1 in direct_flights[city2])))

    # Total days per city
    # Prague: 2 days
    s.add(Sum([If(presence[d][city_idx['Prague']], 1, 0) for d in range(n_days)]) == 2)

    # Berlin: 3 days, including day 6 and 8 (1-based)
    s.add(Sum([If(presence[d][city_idx['Berlin']], 1, 0) for d in range(n_days)]) == 3)
    s.add(presence[5][city_idx['Berlin']])  # Day 6
    s.add(presence[7][city_idx['Berlin']])  # Day 8

    # Tallinn: 5 days, days 8-12 (1-based) must be in Tallinn
    s.add(Sum([If(presence[d][city_idx['Tallinn']], 1, 0) for d in range(n_days)]) == 5)
    for d in range(7, 12):  # days 8-12 (0-based 7-11)
        s.add(presence[d][city_idx['Tallinn']])

    # Stockholm: 5 days
    s.add(Sum([If(presence[d][city_idx['Stockholm']], 1, 0) for d in range(n_days)]) == 5)

    if s.check() == sat:
        model = s.model()
        itinerary = []

        # For each day, determine which cities are present
        days_presence = []
        for day in range(n_days):
            present = []
            for c in range(len(cities)):
                if model.evaluate(presence[day][c]):
                    present.append(cities[c])
            days_presence.append(present)

        # Build the itinerary
        current_stays = {}  # city: start_day

        for day in range(n_days):
            day_num = day + 1
            present_cities = days_presence[day]

            # End stays for cities not present today
            for city in list(current_stays.keys()):
                if city not in present_cities:
                    start = current_stays[city]
                    itinerary.append({"day_range": f"Day {start}-{day_num - 1}", "place": city})
                    del current_stays[city]

            # Handle flight days (two cities)
            if len(present_cities) == 2:
                city1, city2 = present_cities
                itinerary.append({"day_range": f"Day {day_num}", "place": city1})
                itinerary.append({"day_range": f"Day {day_num}", "place": city2})

            # Start new stays for cities not already in current_stays
            for city in present_cities:
                if city not in current_stays:
                    current_stays[city] = day_num

        # Add remaining stays after last day
        for city, start in current_stays.items():
            itinerary.append({"day_range": f"Day {start}-{n_days}", "place": city})

        # Sort itinerary by day
        def day_key(entry):
            parts = entry['day_range'].split('-')
            start_day = int(parts[0][4:])
            return start_day

        itinerary.sort(key=day_key)

        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))