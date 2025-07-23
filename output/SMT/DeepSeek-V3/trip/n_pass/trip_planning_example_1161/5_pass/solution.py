from z3 import *

def solve_scheduling_problem():
    # Cities with their indices
    cities = ["Oslo", "Krakow", "Vilnius", "Helsinki", "Dubrovnik", "Madrid", "Mykonos", "Paris"]
    city_to_int = {city: i for i, city in enumerate(cities)}
    int_to_city = {i: city for i, city in enumerate(cities)}

    # Direct flight connections (bidirectional)
    direct_flights = [
        ("Oslo", "Krakow"),
        ("Oslo", "Paris"),
        ("Paris", "Madrid"),
        ("Helsinki", "Vilnius"),
        ("Oslo", "Madrid"),
        ("Oslo", "Helsinki"),
        ("Helsinki", "Krakow"),
        ("Dubrovnik", "Helsinki"),
        ("Dubrovnik", "Madrid"),
        ("Oslo", "Dubrovnik"),
        ("Krakow", "Paris"),
        ("Madrid", "Mykonos"),
        ("Oslo", "Vilnius"),
        ("Krakow", "Vilnius"),
        ("Helsinki", "Paris"),
        ("Vilnius", "Paris"),
        ("Helsinki", "Madrid")
    ]

    # Create flight connections set
    flight_connections = set()
    for a, b in direct_flights:
        flight_connections.add((city_to_int[a], city_to_int[b]))
        flight_connections.add((city_to_int[b], city_to_int[a]))

    # Initialize solver
    s = Solver()

    # Day variables (1-18)
    days = [Int(f"day_{i}") for i in range(1, 19)]
    for day in days:
        s.add(day >= 0, day < len(cities))

    # Helper function to count days in a city
    def count_days(city_name, days_list):
        city_idx = city_to_int[city_name]
        return sum([If(d == city_idx, 1, 0) for d in days_list])

    # Mykonos: 4 days between day 15-18 (indices 14-17)
    mykonos_days = count_days("Mykonos", days[14:18])
    s.add(mykonos_days == 4)

    # Krakow: 5 days total
    krakow_days = count_days("Krakow", days)
    s.add(krakow_days == 5)

    # Vilnius: 2 days
    vilnius_days = count_days("Vilnius", days)
    s.add(vilnius_days == 2)

    # Helsinki: 2 days
    helsinki_days = count_days("Helsinki", days)
    s.add(helsinki_days == 2)

    # Dubrovnik: 3 days with show on days 2-4 (indices 1-3)
    dubrovnik_days = count_days("Dubrovnik", days)
    s.add(dubrovnik_days == 3)
    s.add(And([days[i] == city_to_int["Dubrovnik"] for i in range(1, 4)]))

    # Oslo: 2 days with friends on day 1 or 2 (indices 0-1)
    oslo_days = count_days("Oslo", days)
    s.add(oslo_days == 2)
    s.add(Or(days[0] == city_to_int["Oslo"], days[1] == city_to_int["Oslo"]))

    # Madrid: 5 days
    madrid_days = count_days("Madrid", days)
    s.add(madrid_days == 5)

    # Paris: 2 days
    paris_days = count_days("Paris", days)
    s.add(paris_days == 2)

    # Flight constraints between consecutive days
    for i in range(17):
        current = days[i]
        next_day = days[i+1]
        same_city = current == next_day
        flight_possible = Or([And(current == a, next_day == b) for (a, b) in flight_connections])
        s.add(Or(same_city, flight_possible))

    # Additional constraints to help solver
    # Prevent staying more than 3 consecutive days in same city
    for i in range(15):
        s.add(Not(And([days[i+j] == days[i] for j in range(4)])))

    # Check solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(18):
            day_num = i + 1
            city_idx = model.evaluate(days[i]).as_long()
            city = int_to_city[city_idx]
            itinerary.append({"day": day_num, "place": city})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print result
import json
result = solve_scheduling_problem()
print(json.dumps(result, indent=2))