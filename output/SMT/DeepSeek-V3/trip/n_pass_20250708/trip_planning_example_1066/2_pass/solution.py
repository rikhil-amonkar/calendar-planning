from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Brussels": 4,
        "Bucharest": 3,
        "Stuttgart": 4,
        "Mykonos": 2,
        "Madrid": 2,
        "Helsinki": 5,
        "Split": 3,
        "London": 5
    }
    
    # Direct flights (bidirectional)
    direct_flights = [
        ("Helsinki", "London"),
        ("Split", "Madrid"),
        ("Helsinki", "Madrid"),
        ("London", "Madrid"),
        ("Brussels", "London"),
        ("Bucharest", "London"),
        ("Brussels", "Bucharest"),
        ("Bucharest", "Madrid"),
        ("Split", "Helsinki"),
        ("Mykonos", "Madrid"),
        ("Stuttgart", "London"),
        ("Helsinki", "Brussels"),
        ("Brussels", "Madrid"),
        ("Split", "London"),
        ("Stuttgart", "Split"),
        ("London", "Mykonos")
    ]
    
    # Create a dictionary for easy lookup
    flight_dict = {}
    for a, b in direct_flights:
        if a not in flight_dict:
            flight_dict[a] = []
        if b not in flight_dict:
            flight_dict[b] = []
        flight_dict[a].append(b)
        flight_dict[b].append(a)
    
    # Total days
    total_days = 21
    
    # Create Z3 solver
    s = Solver()
    
    # Variables: for each day, which city are we in?
    # day 1 to day 21
    day_city = [Int(f"day_{i}_city") for i in range(1, total_days + 1)]
    
    # Assign each city a unique integer
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_cities = {idx: city for city, idx in city_ids.items()}
    
    # Constraints: each day_city must be a valid city id
    for day in day_city:
        s.add(Or([day == city_ids[city] for city in cities]))
    
    # Constraints: consecutive days must be either the same city or connected by a direct flight
    for i in range(total_days - 1):
        current_city = day_city[i]
        next_city = day_city[i + 1]
        s.add(Or(
            current_city == next_city,
            Or([And(current_city == city_ids[a], next_city == city_ids[b]) for a, b in direct_flights])
        )
    
    # Constraints: total days in each city must match the required days
    for city, days in cities.items():
        s.add(Sum([If(day == city_ids[city], 1, 0) for day in day_city]) == days)
    
    # Constraint: Stuttgart must be visited between day 1 and day 4
    s.add(Or([day_city[i] == city_ids["Stuttgart"] for i in range(4)]))
    
    # Constraint: Madrid must be on day 20 and day 21
    s.add(day_city[19] == city_ids["Madrid"])  # day 20
    s.add(day_city[20] == city_ids["Madrid"])  # day 21
    
    # Solve the problem
    if s.check() == sat:
        m = s.model()
        itinerary = []
        current_city = None
        start_day = 1
        for i in range(total_days):
            city_id = m.evaluate(day_city[i]).as_long()
            city = id_cities[city_id]
            if city != current_city:
                if current_city is not None:
                    itinerary.append({
                        "day_range": f"Day {start_day}-{i}",
                        "place": current_city
                    })
                    itinerary.append({
                        "day_range": f"Day {i}",
                        "place": current_city
                    })
                    itinerary.append({
                        "day_range": f"Day {i}",
                        "place": city
                    })
                start_day = i + 1
                current_city = city
        itinerary.append({
            "day_range": f"Day {start_day}-{total_days}",
            "place": current_city
        })
        
        # Verify the itinerary meets all constraints
        days_spent = {city: 0 for city in cities}
        for entry in itinerary:
            place = entry["place"]
            day_range = entry["day_range"]
            if '-' in day_range:
                start, end = map(int, day_range.replace('Day ', '').split('-'))
                days = end - start + 1
            else:
                days = 1
            days_spent[place] += days
        
        valid = True
        for city, days in cities.items():
            if days_spent[city] != days:
                valid = False
                break
        
        if valid:
            return {"itinerary": itinerary}
        else:
            return {"error": "Generated itinerary does not meet all constraints."}
    else:
        return {"error": "No valid itinerary found."}

# Execute the function and print the result
result = solve_itinerary()
print(json.dumps(result, indent=2))