import json
from z3 import *

def solve_itinerary():
    # Define cities and required days
    cities = {
        "Brussels": 3,
        "Helsinki": 3,
        "Split": 4,
        "Dubrovnik": 2,
        "Istanbul": 5,
        "Milan": 4,
        "Vilnius": 5,
        "Frankfurt": 3
    }

    # Direct flights (bidirectional)
    direct_flights = [
        ("Milan", "Frankfurt"),
        ("Split", "Frankfurt"),
        ("Milan", "Split"),
        ("Brussels", "Vilnius"),
        ("Brussels", "Helsinki"),
        ("Istanbul", "Brussels"),
        ("Milan", "Vilnius"),
        ("Brussels", "Milan"),
        ("Istanbul", "Helsinki"),
        ("Helsinki", "Vilnius"),
        ("Helsinki", "Dubrovnik"),
        ("Split", "Vilnius"),
        ("Dubrovnik", "Istanbul"),
        ("Istanbul", "Milan"),
        ("Helsinki", "Frankfurt"),
        ("Istanbul", "Vilnius"),
        ("Split", "Helsinki"),
        ("Milan", "Helsinki"),
        ("Istanbul", "Frankfurt"),
        ("Brussels", "Frankfurt"),
        ("Dubrovnik", "Frankfurt"),
        ("Frankfurt", "Vilnius")
    ]

    # Create flight connections (bidirectional)
    flight_connections = set()
    for city1, city2 in direct_flights:
        flight_connections.add((city1, city2))
        flight_connections.add((city2, city1))

    # Initialize solver with timeout
    s = Solver()
    s.set("timeout", 30000)  # 30 second timeout

    # Create day variables
    city_names = list(cities.keys())
    city_to_idx = {city: idx for idx, city in enumerate(city_names)}
    days = [Int(f"day_{i}") for i in range(1, 23)]

    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == city_to_idx[city] for city in city_names]))

    # Total days per city constraint
    for city, req_days in cities.items():
        s.add(Sum([If(day == city_to_idx[city], 1, 0) for day in days) == req_days)

    # Fixed events:
    # Istanbul days 1-5
    for i in range(5):
        s.add(days[i] == city_to_idx["Istanbul"])

    # Vilnius between days 18-22 (workshop)
    s.add(Or([days[i] == city_to_idx["Vilnius"] for i in range(17, 22)]))

    # Frankfurt between days 16-18 (wedding)
    s.add(Or([days[i] == city_to_idx["Frankfurt"] for i in range(15, 18)]))

    # Flight connectivity constraints (optimized)
    for i in range(len(days)-1):
        current = days[i]
        next_day = days[i+1]
        
        # Either stay or fly to connected city
        stay = current == next_day
        fly = Or([And(current == city_to_idx[c1], next_day == city_to_idx[c2]) 
                for c1, c2 in flight_connections])
        s.add(Or(stay, fly))

    # Add strategic assumptions to help solver:
    # 1. After Istanbul, likely go to Brussels or Helsinki
    if len(days) > 5:
        s.add(Or(
            days[5] == city_to_idx["Brussels"],
            days[5] == city_to_idx["Helsinki"],
            days[5] == city_to_idx["Milan"]
        ))

    # 2. Before Vilnius, likely come from Helsinki or Frankfurt
    for i in range(16, 21):
        s.add(Implies(
            days[i+1] == city_to_idx["Vilnius"],
            Or(
                days[i] == city_to_idx["Helsinki"],
                days[i] == city_to_idx["Frankfurt"],
                days[i] == city_to_idx["Brussels"]
            )
        ))

    # Solve with timeout
    result = s.check()
    if result == sat:
        model = s.model()
        itinerary = []
        for i in range(22):
            day_num = i + 1
            city_idx = model.evaluate(days[i]).as_long()
            city = city_names[city_idx]
            itinerary.append({"day": day_num, "place": city})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found within time limit"}

# Execute and print result
result = solve_itinerary()
print(json.dumps(result, indent=2))