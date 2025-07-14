import json
from z3 import *

def solve_itinerary():
    # Cities
    cities = ["Porto", "Geneva", "Mykonos", "Manchester", "Hamburg", "Naples", "Frankfurt"]
    city_to_int = {city: i for i, city in enumerate(cities)}
    int_to_city = {i: city for i, city in enumerate(cities)}

    # Direct flights (undirected)
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

    # Create a dictionary of direct flight connections
    flight_pairs = {}
    for city in cities:
        connected = []
        for a, b in direct_flights:
            if a == city:
                connected.append(b)
            elif b == city:
                connected.append(a)
        flight_pairs[city] = list(set(connected))

    # Required days in each city
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

    # Z3 variables: each day's city
    days = [Int(f'day_{i}') for i in range(1, total_days + 1)]

    s = Solver()

    # Each day's city must be one of the seven cities
    for day in days:
        s.add(Or([day == city_to_int[city] for city in cities]))

    # Total days per city
    for city in cities:
        s.add(Sum([If(day == city_to_int[city], 1, 0) for day in days]) == required_days[city])

    # Frankfurt show on day 5-6
    s.add(days[4] == city_to_int["Frankfurt"])  # day 5
    s.add(days[5] == city_to_int["Frankfurt"])  # day 6

    # Mykonos friend meeting between day 10-12
    s.add(Or(
        days[9] == city_to_int["Mykonos"],  # day 10
        days[10] == city_to_int["Mykonos"],  # day 11
        days[11] == city_to_int["Mykonos"]   # day 12
    ))

    # Manchester wedding between day 15-18
    s.add(Or(
        days[14] == city_to_int["Manchester"],
        days[15] == city_to_int["Manchester"],
        days[16] == city_to_int["Manchester"],
        days[17] == city_to_int["Manchester"]
    ))

    # Flight transitions
    for i in range(total_days - 1):
        current_city = days[i]
        next_city = days[i + 1]
        # If different, must have a direct flight
        s.add(Implies(
            current_city != next_city,
            Or([And(current_city == city_to_int[a], next_city == city_to_int[b])
                for a in cities for b in flight_pairs.get(a, [])])
        ))

    if s.check() == sat:
        m = s.model()
        day_assignments = []
        for i in range(total_days):
            day_num = i + 1
            city_idx = m.evaluate(days[i]).as_long()
            city = int_to_city[city_idx]
            day_assignments.append((day_num, city))

        # Generate the itinerary with flight days
        itinerary = []
        current_city = day_assignments[0][1]
        start_day = 1
        for i in range(1, total_days):
            day_num, city = day_assignments[i]
            if city != current_city:
                # Add the stay before the flight
                if start_day < i:
                    itinerary.append({"day_range": f"Day {start_day}-{i}", "place": current_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                # Add the flight day: departure and arrival
                itinerary.append({"day_range": f"Day {i}", "place": current_city})
                itinerary.append({"day_range": f"Day {i}", "place": city})
                current_city = city
                start_day = i + 1
        # Add the last stay
        if start_day <= total_days:
            if start_day == total_days:
                itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
            else:
                itinerary.append({"day_range": f"Day {start_day}-{total_days}", "place": current_city})

        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found."}

# Execute the solver
result = solve_itinerary()
print(json.dumps(result, indent=2))