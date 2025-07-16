import json
from z3 import *

def solve_itinerary():
    # Cities with correct spelling
    cities = ["Porto", "Geneva", "Mykonos", "Manchester", "Hamburg", "Naples", "Frankfurt"]
    city_to_int = {city: i for i, city in enumerate(cities)}
    int_to_city = {i: city for i, city in enumerate(cities)}

    # Corrected direct flights (undirected)
    direct_flights = [
        ("Hamburg", "Frankfurt"),
        ("Naples", "Mykonos"),
        ("Hamburg", "Porto"),
        ("Hamburg", "Geneva"),
        ("Mykonos", "Geneva"),
        ("Frankfurt", "Geneva"),
        ("Frankfurt", "Porto"),
        ("Geneva", "Porto"),
        ("Geneva", "Manchester"),
        ("Naples", "Manchester"),
        ("Frankfurt", "Naples"),
        ("Frankfurt", "Manchester"),
        ("Naples", "Geneva"),
        ("Porto", "Manchester"),
        ("Hamburg", "Manchester")
    ]

    # Create flight connections dictionary
    flight_connections = {city: set() for city in cities}
    for a, b in direct_flights:
        flight_connections[a].add(b)
        flight_connections[b].add(a)

    # Required days per city
    required_days = {
        "Porto": 2,
        "Geneva": 3,
        "Mykonos": 3,
        "Manchester": 4,
        "Hamburg": 5,
        "Naples": 5,
        "Frankfurt": 2
    }

    total_days = 18

    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(1, total_days + 1)]
    s = Solver()

    # Each day must be assigned to a valid city
    for day in days:
        s.add(Or([day == city_to_int[city] for city in cities]))

    # Total days per city constraint
    for city in cities:
        s.add(Sum([If(day == city_to_int[city], 1, 0) for day in days]) == required_days[city])

    # Frankfurt show on days 5-6
    s.add(days[4] == city_to_int["Frankfurt"])  # Day 5
    s.add(days[5] == city_to_int["Frankfurt"])  # Day 6

    # Mykonos friend meeting between days 10-12
    s.add(Or(
        days[9] == city_to_int["Mykonos"],   # Day 10
        days[10] == city_to_int["Mykonos"],  # Day 11
        days[11] == city_to_int["Mykonos"]   # Day 12
    ))

    # Manchester wedding between days 15-18
    s.add(Or(
        days[14] == city_to_int["Manchester"],  # Day 15
        days[15] == city_to_int["Manchester"],  # Day 16
        days[16] == city_to_int["Manchester"],  # Day 17
        days[17] == city_to_int["Manchester"]   # Day 18
    ))

    # Flight transition constraints
    for i in range(total_days - 1):
        current = days[i]
        next_day = days[i + 1]
        s.add(Implies(
            current != next_day,
            Or([And(current == city_to_int[a], next_day == city_to_int[b])
               for a in cities for b in flight_connections[a]])
        ))

    # Additional constraints to help the solver
    # Ensure at least 2 consecutive days in Frankfurt for the show
    s.add(days[4] == days[5])  # Days 5-6 same city

    # Try to find a solution
    if s.check() == sat:
        m = s.model()
        day_assignments = []
        for i in range(total_days):
            day_num = i + 1
            city_idx = m.evaluate(days[i]).as_long()
            city = int_to_city[city_idx]
            day_assignments.append((day_num, city))

        # Generate itinerary with flight days
        itinerary = []
        current_city = day_assignments[0][1]
        start_day = 1
        for i in range(1, total_days):
            day_num, city = day_assignments[i]
            if city != current_city:
                # Add stay before flight
                if start_day < i:
                    itinerary.append({"day_range": f"Day {start_day}-{i}", "place": current_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                # Add flight day (departure and arrival)
                itinerary.append({"day_range": f"Day {i}", "place": current_city})
                itinerary.append({"day_range": f"Day {i}", "place": city})
                current_city = city
                start_day = i + 1
        # Add final stay
        if start_day <= total_days:
            if start_day == total_days:
                itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
            else:
                itinerary.append({"day_range": f"Day {start_day}-{total_days}", "place": current_city})

        return {"itinerary": itinerary}
    else:
        # If no solution found, try relaxing some constraints
        print("No strict solution found. Trying relaxed constraints...")
        # Relax Naples days from 5 to 4
        s.reset()
        required_days["Naples"] = 4
        for city in cities:
            s.add(Sum([If(day == city_to_int[city], 1, 0) for day in days]) == required_days[city])
        # Keep other constraints
        s.add(days[4] == city_to_int["Frankfurt"])
        s.add(days[5] == city_to_int["Frankfurt"])
        s.add(Or(days[9] == city_to_int["Mykonos"], days[10] == city_to_int["Mykonos"], days[11] == city_to_int["Mykonos"]))
        s.add(Or(days[14] == city_to_int["Manchester"], days[15] == city_to_int["Manchester"], 
               days[16] == city_to_int["Manchester"], days[17] == city_to_int["Manchester"]))
        for i in range(total_days - 1):
            current = days[i]
            next_day = days[i + 1]
            s.add(Implies(current != next_day,
                         Or([And(current == city_to_int[a], next_day == city_to_int[b])
                            for a in cities for b in flight_connections[a]])))
        
        if s.check() == sat:
            m = s.model()
            day_assignments = []
            for i in range(total_days):
                day_num = i + 1
                city_idx = m.evaluate(days[i]).as_long()
                city = int_to_city[city_idx]
                day_assignments.append((day_num, city))

            itinerary = []
            current_city = day_assignments[0][1]
            start_day = 1
            for i in range(1, total_days):
                day_num, city = day_assignments[i]
                if city != current_city:
                    if start_day < i:
                        itinerary.append({"day_range": f"Day {start_day}-{i}", "place": current_city})
                    else:
                        itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                    itinerary.append({"day_range": f"Day {i}", "place": current_city})
                    itinerary.append({"day_range": f"Day {i}", "place": city})
                    current_city = city
                    start_day = i + 1
            if start_day <= total_days:
                if start_day == total_days:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{total_days}", "place": current_city})

            return {"itinerary": itinerary, "note": "Relaxed Naples days to 4 to find solution"}
        else:
            return {"error": "No valid itinerary found even with relaxed constraints"}

# Execute the solver
result = solve_itinerary()
print(json.dumps(result, indent=2))