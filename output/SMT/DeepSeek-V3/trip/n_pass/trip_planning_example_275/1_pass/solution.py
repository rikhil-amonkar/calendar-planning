from z3 import *

def solve_itinerary():
    # Define the cities with unique integers
    cities = {
        'Split': 0,
        'Vilnius': 1,
        'Madrid': 2,
        'Santorini': 3
    }
    inv_cities = {v: k for k, v in cities.items()}

    # Direct flights: adjacency list
    direct_flights = {
        cities['Vilnius']: [cities['Split']],
        cities['Split']: [cities['Vilnius'], cities['Madrid']],
        cities['Madrid']: [cities['Split'], cities['Santorini']],
        cities['Santorini']: [cities['Madrid']]
    }

    # Create a solver instance
    s = Solver()

    # Variables: city per day (days 1..14)
    day_city = [Int(f'day_{i}_city') for i in range(1, 15)]

    # Constraint: each day_city must be one of the cities
    for i in range(14):
        s.add(Or([day_city[i] == c for c in cities.values()]))

    # Fixed days 13 and 14 in Santorini
    s.add(day_city[12] == cities['Santorini'])  # day 13
    s.add(day_city[13] == cities['Santorini'])  # day 14

    # Constraints on transitions between days: consecutive days must be same city or connected by direct flight
    for i in range(13):  # days 1..13 transitions to next day
        current = day_city[i]
        next_day = day_city[i+1]
        s.add(Or(
            current == next_day,  # stay in the same city
            And(current != next_day, next_day in direct_flights[current])  # direct flight
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
        
        # Now, process the itinerary_days to create the JSON output
        itinerary = []
        current_place = itinerary_days[0]
        start_day = 1
        
        for i in range(1, 14):
            if itinerary_days[i] != current_place:
                # Add the stay before the flight
                if start_day == i:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{i}", "place": current_place})
                # Add the flight day (departure and arrival)
                itinerary.append({"day_range": f"Day {i+1}", "place": current_place})
                itinerary.append({"day_range": f"Day {i+1}", "place": itinerary_days[i]})
                current_place = itinerary_days[i]
                start_day = i + 1
        # Add the last segment
        if start_day <= 14:
            if start_day == 14:
                itinerary.append({"day_range": f"Day 14", "place": current_place})
            else:
                itinerary.append({"day_range": f"Day {start_day}-14", "place": current_place})
        
        # Now, create the JSON output
        output = {"itinerary": itinerary}
        return output
    else:
        return {"error": "No valid itinerary found"}

# Execute the function and print the result
result = solve_itinerary()
print(result)