import json
from z3 import *

def solve_itinerary():
    # Define cities and required days
    cities = {
        "Vienna": 4,
        "Barcelona": 2,
        "Edinburgh": 4,
        "Krakow": 3,
        "Riga": 4,
        "Hamburg": 2,
        "Paris": 2,
        "Stockholm": 2
    }

    # Define all direct flight connections (bidirectional)
    direct_flights = [
        ("Hamburg", "Stockholm"),
        ("Vienna", "Stockholm"),
        ("Paris", "Edinburgh"),
        ("Riga", "Barcelona"),
        ("Paris", "Riga"),
        ("Krakow", "Barcelona"),
        ("Edinburgh", "Stockholm"),
        ("Paris", "Krakow"),
        ("Krakow", "Stockholm"),
        ("Riga", "Edinburgh"),
        ("Barcelona", "Stockholm"),
        ("Paris", "Stockholm"),
        ("Krakow", "Edinburgh"),
        ("Vienna", "Hamburg"),
        ("Paris", "Hamburg"),
        ("Riga", "Stockholm"),
        ("Hamburg", "Barcelona"),
        ("Vienna", "Barcelona"),
        ("Krakow", "Vienna"),
        ("Riga", "Hamburg"),
        ("Barcelona", "Edinburgh"),
        ("Paris", "Barcelona"),
        ("Hamburg", "Edinburgh"),
        ("Paris", "Vienna"),
        ("Vienna", "Riga")
    ]

    # Create bidirectional flight connections
    flight_connections = set()
    for a, b in direct_flights:
        flight_connections.add((a, b))
        flight_connections.add((b, a))

    # Create solver
    s = Solver()

    # Days are 1..16
    days = 16
    day_numbers = range(1, days + 1)

    # Create variables: for each day, which city are we in?
    city_vars = [Int(f"day_{i}") for i in day_numbers]

    # Assign each city a unique integer
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}

    # Constraints: each day's variable must be one of the city IDs
    for day_var in city_vars:
        s.add(Or([day_var == city_ids[city] for city in cities]))

    # Specific event constraints:
    # Wedding in Paris on day 1 and 2
    s.add(city_vars[0] == city_ids["Paris"])
    s.add(city_vars[1] == city_ids["Paris"])

    # Conference in Hamburg on day 10 and 11
    s.add(city_vars[9] == city_ids["Hamburg"])
    s.add(city_vars[10] == city_ids["Hamburg"])

    # Meet friend in Edinburgh between day 12 and 15
    s.add(Or([city_vars[i] == city_ids["Edinburgh"] for i in range(11, 14 + 1)]))

    # Visit relatives in Stockholm between day 15 and 16
    s.add(Or(city_vars[14] == city_ids["Stockholm"], city_vars[15] == city_ids["Stockholm"]))

    # Flight constraints: consecutive days must be same city or connected by a direct flight
    for i in range(days - 1):
        current_day = city_vars[i]
        next_day = city_vars[i + 1]
        s.add(Or(
            current_day == next_day,
            *[
                And(current_day == city_ids[a], next_day == city_ids[b])
                for (a, b) in flight_connections
            ]
        ))

    # Total days in each city must match requirements
    for city, required_days in cities.items():
        city_id = city_ids[city]
        total_days = Sum([If(city_vars[i] == city_id, 1, 0) for i in range(days)])
        s.add(total_days == required_days)

    # Solve the problem
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(days):
            city_id = m.evaluate(city_vars[i]).as_long()
            city = id_to_city[city_id]
            itinerary.append({"day": i + 1, "place": city})
        
        # Verify all constraints are satisfied
        city_days = {city: 0 for city in cities}
        for entry in itinerary:
            city_days[entry["place"]] += 1
        
        for city, required in cities.items():
            assert city_days[city] == required, f"City {city} has {city_days[city]} days instead of {required}"
        
        # Verify specific events
        assert itinerary[0]["place"] == "Paris" and itinerary[1]["place"] == "Paris"
        assert itinerary[9]["place"] == "Hamburg" and itinerary[10]["place"] == "Hamburg"
        assert any(itinerary[i]["place"] == "Edinburgh" for i in range(11, 14 + 1))
        assert itinerary[14]["place"] == "Stockholm" or itinerary[15]["place"] == "Stockholm"
        
        # Verify flight connections
        for i in range(days - 1):
            current = itinerary[i]["place"]
            next_ = itinerary[i + 1]["place"]
            if current != next_:
                assert (current, next_) in flight_connections, f"No flight from {current} to {next_} on day {i + 1}"
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Run the solver and print the result
result = solve_itinerary()
print(json.dumps(result, indent=2))