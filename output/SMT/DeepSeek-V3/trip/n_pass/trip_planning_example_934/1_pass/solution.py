import json
from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Brussels': 5,
        'Rome': 2,
        'Dubrovnik': 3,
        'Geneva': 5,
        'Budapest': 2,
        'Riga': 4,
        'Valencia': 2
    }
    city_list = list(cities.keys())
    total_days = 17

    # Direct flights as adjacency list
    flights = {
        'Brussels': ['Valencia', 'Geneva', 'Riga', 'Rome', 'Budapest'],
        'Rome': ['Valencia', 'Geneva', 'Riga', 'Budapest', 'Brussels', 'Dubrovnik'],
        'Dubrovnik': ['Geneva', 'Rome'],
        'Geneva': ['Brussels', 'Rome', 'Dubrovnik', 'Valencia', 'Budapest'],
        'Budapest': ['Geneva', 'Rome', 'Brussels'],
        'Riga': ['Rome', 'Brussels'],
        'Valencia': ['Brussels', 'Rome', 'Geneva']
    }

    # Create Z3 variables for each day (1-based)
    day_vars = [Int(f'day_{i}') for i in range(1, total_days + 1)]
    s = Solver()

    # Each day variable is an index corresponding to city_list
    for day in day_vars:
        s.add(day >= 0, day < len(city_list))

    # Constraint: total days per city must match requirements
    for city_idx, city in enumerate(city_list):
        s.add(Sum([If(day == city_idx, 1, 0) for day in day_vars]) == cities[city])

    # Brussels must be visited between day 7 and 11 (inclusive)
    brussels_idx = city_list.index('Brussels')
    s.add(Or([day_vars[i] == brussels_idx for i in range(6, 11)]))

    # Budapest must be visited on day 16 or 17 (meeting friend between 16-17)
    budapest_idx = city_list.index('Budapest')
    s.add(Or(day_vars[15] == budapest_idx, day_vars[16] == budapest_idx))

    # Riga must be visited between day 4 and 7 (inclusive)
    riga_idx = city_list.index('Riga')
    s.add(Or([day_vars[i] == riga_idx for i in range(3, 7)]))

    # Flight constraints: consecutive days must be same city or connected by direct flight
    for i in range(total_days - 1):
        current_city = day_vars[i]
        next_city = day_vars[i + 1]
        # Either stay in the same city or move to a connected city
        same_city = (current_city == next_city)
        connected = Or([And(current_city == city_list.index(c), next_city == city_list.index(n))
                       for c in flights for n in flights[c]])
        s.add(Or(same_city, connected))

    if s.check() == sat:
        model = s.model()
        day_assignments = [model.evaluate(day).as_long() for day in day_vars]
        itinerary = []

        current_city = city_list[day_assignments[0]]
        start_day = 1
        for day in range(1, total_days):
            if city_list[day_assignments[day]] == current_city:
                continue
            else:
                end_day = day + 1
                if start_day == end_day - 1:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{end_day - 1}", "place": current_city})
                # Flight day: add departure and arrival
                itinerary.append({"day_range": f"Day {end_day - 1}", "place": current_city})
                next_city = city_list[day_assignments[day]]
                itinerary.append({"day_range": f"Day {end_day - 1}", "place": next_city})
                current_city = next_city
                start_day = end_day
        # Add the last stay
        if start_day <= total_days:
            end_day = total_days
            if start_day == end_day:
                itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
            else:
                itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": current_city})

        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))