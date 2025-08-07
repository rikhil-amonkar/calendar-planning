from z3 import Solver, Int, Or, And, If, sat
import json

def main():
    cities = ["Zurich", "Hamburg", "Helsinki", "Bucharest", "Split"]
    city_to_index = {city: idx for idx, city in enumerate(cities)}
    
    # Create directed flight connections (bidirectional)
    flight_edges = []
    undirected_connections = [
        ("Zurich", "Helsinki"),
        ("Hamburg", "Bucharest"),
        ("Helsinki", "Hamburg"),
        ("Zurich", "Hamburg"),
        ("Zurich", "Bucharest"),
        ("Zurich", "Split"),
        ("Helsinki", "Split"),
        ("Split", "Hamburg")
    ]
    for city1, city2 in undirected_connections:
        idx1 = city_to_index[city1]
        idx2 = city_to_index[city2]
        flight_edges.append((idx1, idx2))
        flight_edges.append((idx2, idx1))
    
    required_days = {
        "Zurich": 3,
        "Hamburg": 2,
        "Helsinki": 2,
        "Bucharest": 2,
        "Split": 7
    }
    
    s = Solver()
    
    # Decision variables: city index for each day (0-11)
    day_assignments = [Int(f"day_{i}") for i in range(12)]
    for day in range(12):
        s.add(day_assignments[day] >= 0, day_assignments[day] < 5)
    
    # Conference constraints: must be in Split on day 4 and day 10
    s.add(day_assignments[3] == city_to_index["Split"])  # Day 4 (index 3)
    s.add(day_assignments[9] == city_to_index["Split"])  # Day 10 (index 9)
    
    # Wedding constraint: must be in Zurich on at least one of first 3 days
    s.add(Or(
        day_assignments[0] == city_to_index["Zurich"],
        day_assignments[1] == city_to_index["Zurich"],
        day_assignments[2] == city_to_index["Zurich"]
    ))
    
    # Flight connection constraints between consecutive days
    for day in range(11):
        current_city = day_assignments[day]
        next_city = day_assignments[day + 1]
        # Allow staying in same city OR direct flight connection
        s.add(Or(
            current_city == next_city,
            Or([And(current_city == u, next_city == v) for u, v in flight_edges])
        ))
    
    # Total days per city constraint
    for city, req_days in required_days.items():
        city_idx = city_to_index[city]
        total = 0
        for day in range(12):
            total += If(day_assignments[day] == city_idx, 1, 0)
        s.add(total == req_days)
    
    if s.check() == sat:
        model = s.model()
        assignments = [model.evaluate(day_assignments[i]).as_long() for i in range(12)]
        
        # Build itinerary by grouping consecutive days
        itinerary = []
        current_city = assignments[0]
        start_day = 1
        for day in range(1, 12):
            if assignments[day] != current_city:
                itinerary.append({
                    "day_range": f"Day {start_day}-{day}",
                    "place": cities[current_city]
                })
                current_city = assignments[day]
                start_day = day + 1
        # Add last segment
        itinerary.append({
            "day_range": f"Day {start_day}-12",
            "place": cities[current_city]
        })
        
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No valid itinerary found")

if __name__ == "__main__":
    main()