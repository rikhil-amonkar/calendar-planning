from z3 import *

def solve_itinerary():
    s = Solver()

    # Total days and city codes
    total_days = 15
    cities = {'Stuttgart': 0, 'Seville': 1, 'Manchester': 2}
    city_names = {v: k for k, v in cities.items()}

    # Create variables for each day's city
    day_city = [Int(f"day_{day}") for day in range(1, total_days + 1)]

    # Each day must be assigned to one of the three cities
    for day in day_city:
        s.add(Or([day == cities[city] for city in cities]))

    # Calculate total days in each city (including overlapping flight days)
    total_S = Sum([If(day == cities['Stuttgart'], 1, 0) for day in day_city])
    total_V = Sum([If(day == cities['Seville'], 1, 0) for day in day_city])
    total_M = Sum([If(day == cities['Manchester'], 1, 0) for day in day_city])

    # Add duration constraints (must be exact matches)
    s.add(total_S == 6)
    s.add(total_V == 7)
    s.add(total_M == 4)

    # Constraint: Must be in Stuttgart between day 1 and 6 (inclusive)
    s.add(Or([day_city[i] == cities['Stuttgart'] for i in range(6)]))

    # Flight transition constraints
    for i in range(total_days - 1):
        current = day_city[i]
        next_day = day_city[i + 1]
        # Possible transitions:
        # Stay in same city
        # Stuttgart <-> Manchester
        # Manchester <-> Seville
        s.add(Or(
            current == next_day,  # Stay in same city
            And(current == cities['Stuttgart'], next_day == cities['Manchester']),
            And(current == cities['Manchester'], next_day == cities['Stuttgart']),
            And(current == cities['Manchester'], next_day == cities['Seville']),
            And(current == cities['Seville'], next_day == cities['Manchester'])
        ))

    # Additional constraint: Cannot have Seville and Stuttgart consecutive without Manchester
    for i in range(total_days - 1):
        current = day_city[i]
        next_day = day_city[i + 1]
        s.add(Not(And(current == cities['Seville'], next_day == cities['Stuttgart'])))
        s.add(Not(And(current == cities['Stuttgart'], next_day == cities['Seville'])))

    # Try to find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(1, total_days + 1):
            city_code = model[day_city[day - 1]].as_long()
            itinerary.append({"day": day, "place": city_names[city_code]})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))