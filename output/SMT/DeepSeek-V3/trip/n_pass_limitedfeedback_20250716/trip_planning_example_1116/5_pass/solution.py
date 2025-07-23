from z3 import *

def solve_scheduling_problem():
    # Define cities with consistent naming
    cities = ["Oslo", "Reykjavik", "Stockholm", "Munich", "Frankfurt", "Barcelona", "Bucharest", "Split"]
    city_to_num = {city: idx for idx, city in enumerate(cities)}
    num_to_city = {idx: city for idx, city in enumerate(cities)}

    # Define direct flights (ensuring consistent city names)
    direct_flights = {
        ("Reykjavik", "Munich"), ("Munich", "Frankfurt"), ("Split", "Oslo"), ("Reykjavik", "Oslo"),
        ("Bucharest", "Munich"), ("Oslo", "Frankfurt"), ("Bucharest", "Barcelona"), ("Barcelona", "Frankfurt"),
        ("Reykjavik", "Frankfurt"), ("Barcelona", "Stockholm"), ("Barcelona", "Reykjavik"), ("Stockholm", "Reykjavik"),
        ("Barcelona", "Split"), ("Bucharest", "Oslo"), ("Bucharest", "Frankfurt"), ("Split", "Stockholm"),
        ("Barcelona", "Oslo"), ("Stockholm", "Munich"), ("Stockholm", "Oslo"), ("Split", "Frankfurt"),
        ("Barcelona", "Munich"), ("Stockholm", "Frankfurt"), ("Munich", "Oslo"), ("Split", "Munich")
    }

    # Create symmetric flight connections using city indices
    flight_connections = set()
    for a, b in direct_flights:
        flight_connections.add((city_to_num[a], city_to_num[b]))
        flight_connections.add((city_to_num[b], city_to_num[a]))

    # Initialize solver
    solver = Solver()

    # Create day variables (1-20)
    days = [Int(f"day_{i}") for i in range(1, 21)]
    for day in days:
        solver.add(day >= 0, day < 8)  # 0-7 for 8 cities

    # City duration constraints
    duration_constraints = [
        ("Oslo", 2),
        ("Reykjavik", 5),
        ("Stockholm", 4),
        ("Munich", 4),
        ("Frankfurt", 4),
        ("Barcelona", 3),
        ("Bucharest", 2),
        ("Split", 3)
    ]

    for city, duration in duration_constraints:
        count = Sum([If(day == city_to_num[city], 1, 0) for day in days])
        solver.add(count == duration)

    # Specific day constraints
    # Oslo on days 16-17 (indices 15-16)
    solver.add(days[15] == city_to_num["Oslo"])
    solver.add(days[16] == city_to_num["Oslo"])

    # Reykjavik between days 9-13 (indices 8-12)
    solver.add(Or([days[i] == city_to_num["Reykjavik"] for i in range(8, 13)]))

    # Munich between days 13-16 (indices 12-15)
    solver.add(Or([days[i] == city_to_num["Munich"] for i in range(12, 16)]))

    # Frankfurt between days 17-20 (indices 16-19)
    solver.add(Or([days[i] == city_to_num["Frankfurt"] for i in range(16, 20)]))

    # Flight connection constraints
    for i in range(19):
        current = days[i]
        next_day = days[i+1]
        # Generate all possible flight connections
        flight_options = []
        for a, b in flight_connections:
            flight_options.append(And(current == a, next_day == b))
        solver.add(Or(current == next_day, *flight_options))  # Stay or fly

    # Solve and format output
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(20):
            day_num = i + 1
            city_num = model.evaluate(days[i]).as_long()
            city = num_to_city[city_num]
            itinerary.append({"day": day_num, "place": city})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute and print result
result = solve_scheduling_problem()
print(result)