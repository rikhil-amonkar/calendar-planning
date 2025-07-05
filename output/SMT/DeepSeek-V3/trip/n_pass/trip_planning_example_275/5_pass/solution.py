from z3 import *

def solve_itinerary():
    # Define cities with unique integers
    cities = {
        'Split': 0,
        'Vilnius': 1,
        'Madrid': 2,
        'Santorini': 3
    }
    inv_cities = {v: k for k, v in cities.items()}

    # Direct flights: adjacency list
    direct_flights = {
        0: [1, 2],  # Split can fly to Vilnius and Madrid
        1: [0],      # Vilnius can fly to Split
        2: [0, 3],   # Madrid can fly to Split and Santorini
        3: [2]       # Santorini can fly to Madrid
    }

    # Create solver instance
    s = Solver()

    # Variables: city per day (days 1..14)
    day_city = [Int(f'day_{i}_city') for i in range(1, 15)]

    # Constraint: each day_city must be one of the cities
    for i in range(14):
        s.add(Or([day_city[i] == c for c in cities.values()]))

    # Fixed days 13 and 14 in Santorini
    s.add(day_city[12] == cities['Santorini'])  # day 13
    s.add(day_city[13] == cities['Santorini'])  # day 14

    # Constraints on transitions between days
    for i in range(13):  # days 1..13 transitions to next day
        current = day_city[i]
        next_day = day_city[i+1]
        # Either stay in same city or take direct flight
        s.add(Or(
            current == next_day,
            And(current == cities['Split'], Or(next_day == cities['Vilnius'], next_day == cities['Madrid'])),
            And(current == cities['Vilnius'], next_day == cities['Split']),
            And(current == cities['Madrid'], Or(next_day == cities['Split'], next_day == cities['Santorini'])),
            And(current == cities['Santorini'], next_day == cities['Madrid'])
        ))

    # Total days per city constraints
    total_split = Sum([If(day_city[i] == cities['Split'], 1, 0) for i in range(14)])
    total_vilnius = Sum([If(day_city[i] == cities['Vilnius'], 1, 0) for i in range(14)])
    total_madrid = Sum([If(day_city[i] == cities['Madrid'], 1, 0) for i in range(14)])
    total_santorini = Sum([If(day_city[i] == cities['Santorini'], 1, 0) for i in range(14)])

    s.add(total_split == 5)
    s.add(total_vilnius == 4)
    s.add(total_madrid == 6)
    s.add(total_santorini == 2)  # days 13-14 are already set

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        # Extract the day assignments
        itinerary_days = []
        for i in range(14):
            city_val = m.evaluate(day_city[i]).as_long()
            itinerary_days.append(inv_cities[city_val])
        
        # Process itinerary_days to create JSON output
        itinerary = []
        current_place = itinerary_days[0]
        start_day = 1
        
        for i in range(1, 14):
            if itinerary_days[i] != itinerary_days[i-1]:
                # Add stay before flight
                if start_day == i:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{i}", "place": current_place})
                # Add flight day (departure and arrival)
                itinerary.append({"day_range": f"Day {i+1}", "place": current_place})
                itinerary.append({"day_range": f"Day {i+1}", "place": itinerary_days[i]})
                current_place = itinerary_days[i]
                start_day = i + 1
        # Add last segment
        if start_day <= 14:
            if start_day == 14:
                itinerary.append({"day_range": f"Day 14", "place": current_place})
            else:
                itinerary.append({"day_range": f"Day {start_day}-14", "place": current_place})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print result
result = solve_itinerary()
print(result)