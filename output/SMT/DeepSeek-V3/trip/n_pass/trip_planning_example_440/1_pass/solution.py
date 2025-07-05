from z3 import *

def solve_itinerary():
    # Cities mapping
    cities = {
        'Split': 0,
        'Helsinki': 1,
        'Reykjavik': 2,
        'Vilnius': 3,
        'Geneva': 4
    }
    inv_cities = {v: k for k, v in cities.items()}
    num_days = 12

    # Direct flights: adjacency list. Each entry is (from, to)
    direct_flights = [
        (cities['Split'], cities['Helsinki']),
        (cities['Helsinki'], cities['Split']),
        (cities['Split'], cities['Geneva']),
        (cities['Geneva'], cities['Split']),
        (cities['Geneva'], cities['Helsinki']),
        (cities['Helsinki'], cities['Geneva']),
        (cities['Helsinki'], cities['Reykjavik']),
        (cities['Reykjavik'], cities['Helsinki']),
        (cities['Vilnius'], cities['Helsinki']),
        (cities['Helsinki'], cities['Vilnius']),
        (cities['Split'], cities['Vilnius']),
        (cities['Vilnius'], cities['Split'])
    ]
    # Fixing typos in city names
    direct_flights = [
        (cities['Split'], cities['Helsinki']),
        (cities['Helsinki'], cities['Split']),
        (cities['Split'], cities['Geneva']),
        (cities['Geneva'], cities['Split']),
        (cities['Geneva'], cities['Helsinki']),
        (cities['Helsinki'], cities['Geneva']),
        (cities['Helsinki'], cities['Reykjavik']),
        (cities['Reykjavik'], cities['Helsinki']),
        (cities['Vilnius'], cities['Helsinki']),
        (cities['Helsinki'], cities['Vilnius']),
        (cities['Split'], cities['Vilnius']),
        (cities['Vilnius'], cities['Split'])
    ]
    # Create adjacency list
    adjacency = {c: set() for c in cities.values()}
    for (f, t) in direct_flights:
        adjacency[f].add(t)
        adjacency[t].add(f)  # assuming flights are bidirectional

    # Z3 variables: day[i] is the city on day i+1 (days are 1-based)
    day = [Int(f'day_{i}') for i in range(num_days)]

    s = Solver()

    # Each day must be a valid city
    for d in day:
        s.add(And(d >= 0, d < len(cities)))

    # Constraints for specific days
    # Reykjavik on days 10-12 (indices 9-11)
    for i in [9, 10, 11]:
        s.add(day[i] == cities['Reykjavik'])

    # Vilnius on days 7-9 (indices 6-8)
    for i in [6, 7, 8]:
        s.add(day[i] == cities['Vilnius'])

    # Flight transitions: consecutive days can only change to directly connected cities
    for i in range(num_days - 1):
        current_city = day[i]
        next_city = day[i+1]
        s.add(Or(current_city == next_city, Or([next_city == fc for fc in adjacency[current_city]])))

    # Total days per city constraints
    # Split: 2 days
    split_days = Sum([If(day[i] == cities['Split'], 1, 0) for i in range(num_days)])
    s.add(split_days == 2)

    # Helsinki: 2 days
    helsinki_days = Sum([If(day[i] == cities['Helsinki'], 1, 0) for i in range(num_days)])
    s.add(helsinki_days == 2)

    # Reykjavik: 3 days (already has 3 days in 10-12)
    reykjavik_days = Sum([If(day[i] == cities['Reykjavik'], 1, 0) for i in range(num_days)])
    s.add(reykjavik_days == 3)

    # Vilnius: 3 days (days 7-9)
    vilnius_days = Sum([If(day[i] == cities['Vilnius'], 1, 0) for i in range(num_days)])
    s.add(vilnius_days == 3)

    # Geneva: 6 days
    geneva_days = Sum([If(day[i] == cities['Geneva'], 1, 0) for i in range(num_days)])
    s.add(geneva_days == 6)

    # Check and get model
    if s.check() == sat:
        model = s.model()
        day_assignments = [model.evaluate(day[i]).as_long() for i in range(num_days)]
        
        itinerary = []
        current_city = day_assignments[0]
        start_day = 1
        for i in range(1, num_days):
            if day_assignments[i] != current_city:
                # Add the stay before the flight
                if start_day == i:
                    itinerary.append({"day_range": f"Day {start_day}", "place": inv_cities[current_city]})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{i}", "place": inv_cities[current_city]})
                # Add the flight day for departure city
                itinerary.append({"day_range": f"Day {i}", "place": inv_cities[current_city]})
                # Add the flight day for arrival city
                current_city = day_assignments[i]
                itinerary.append({"day_range": f"Day {i}", "place": inv_cities[current_city]})
                start_day = i + 1
        # Add the last stay
        if start_day <= num_days:
            if start_day == num_days:
                itinerary.append({"day_range": f"Day {start_day}", "place": inv_cities[current_city]})
            else:
                itinerary.append({"day_range": f"Day {start_day}-{num_days}", "place": inv_cities[current_city]})
        
        # Post-process to merge consecutive same-city entries (if any)
        # But the current logic should handle it as per the example.
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))