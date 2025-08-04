from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Porto": 2,
        "Geneva": 3,
        "Mykonos": 3,
        "Manchester": 4,
        "Hamburg": 5,
        "Naples": 5,
        "Frankfurt": 2
    }
    
    # Direct flight connections (bidirectional)
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
    
    # Create flight map
    flight_map = {city: [] for city in cities}
    for a, b in direct_flights:
        flight_map[a].append(b)
        flight_map[b].append(a)
    
    # Days are 1..18
    days = 18
    
    # Create Z3 variables
    itinerary = [Int(f"day_{d}") for d in range(1, days + 1)]
    city_ids = {city: idx for idx, city in enumerate(cities)}
    
    s = Solver()
    
    # Each day must be one of the cities
    for d in range(days):
        s.add(Or([itinerary[d] == city_ids[city] for city in cities]))
    
    # Count days in each city (including flight days)
    for city in cities:
        count = Sum([If(itinerary[d] == city_ids[city], 1, 0) for d in range(days)])
        s.add(count == cities[city])
    
    # Mykonos between day 10-12
    s.add(Or([itinerary[d] == city_ids["Mykonos"] for d in range(9, 12)]))
    
    # Manchester wedding between day 15-18
    s.add(Or([itinerary[d] == city_ids["Manchester"] for d in range(14, 18)]))
    
    # Frankfurt show on day 5 or 6
    s.add(Or(itinerary[4] == city_ids["Frankfurt"], itinerary[5] == city_ids["Frankfurt"]))
    
    # Flight constraints
    for d in range(days - 1):
        current = itinerary[d]
        next_ = itinerary[d + 1]
        # If cities are different, they must be connected
        for city1 in cities:
            for city2 in cities:
                if city1 != city2 and city2 not in flight_map[city1]:
                    s.add(Not(And(current == city_ids[city1], next_ == city_ids[city2])))
    
    # Try to find a solution
    if s.check() == sat:
        m = s.model()
        itinerary_result = []
        city_list = list(cities.keys())
        for d in range(days):
            city_idx = m.evaluate(itinerary[d]).as_long()
            itinerary_result.append({"day": d + 1, "place": city_list[city_idx]})
        
        # Verify all constraints
        counts = {city: 0 for city in cities}
        for entry in itinerary_result:
            counts[entry["place"]] += 1
        
        mykonos_days = [entry["day"] for entry in itinerary_result if entry["place"] == "Mykonos"]
        manchester_days = [entry["day"] for entry in itinerary_result if entry["place"] == "Manchester"]
        frankfurt_days = [entry["day"] for entry in itinerary_result if entry["place"] == "Frankfurt"]
        
        assert all(counts[city] == cities[city] for city in cities)
        assert any(10 <= day <= 12 for day in mykonos_days)
        assert any(15 <= day <= 18 for day in manchester_days)
        assert any(day == 5 or day == 6 for day in frankfurt_days)
        
        # Verify flight connections
        for d in range(days - 1):
            current = itinerary_result[d]["place"]
            next_ = itinerary_result[d + 1]["place"]
            if current != next_:
                assert next_ in flight_map[current]
        
        return {"itinerary": itinerary_result}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))