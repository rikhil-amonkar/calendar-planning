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
    
    # Direct flight connections (undirected)
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
    
    # Create a bidirectional flight map
    flight_map = {city: [] for city in cities}
    for a, b in direct_flights:
        flight_map[a].append(b)
        flight_map[b].append(a)
    
    # Days are 1..18
    days = 18
    Day = 1
    
    # Create Z3 variables: itinerary[d] is the city on day d (1-based)
    itinerary = [Int(f"day_{d}") for d in range(1, days + 1)]
    
    s = Solver()
    
    # Each day must be one of the cities
    city_ids = {city: idx for idx, city in enumerate(cities)}
    for d in range(days):
        s.add(Or([itinerary[d] == city_ids[city] for city in cities]))
    
    # Constraints for days in each city
    for city in cities:
        count = Sum([If(itinerary[d] == city_ids[city], 1, 0) for d in range(days)])
        s.add(count == cities[city])
    
    # Constraints for specific events:
    # Mykonos: must be there between day 10-12 (inclusive)
    s.add(Or([itinerary[d] == city_ids["Mykonos"] for d in range(9, 12)]))  # days 10-12 (1-based: indices 9-11)
    
    # Manchester: wedding between day 15-18
    s.add(Or([itinerary[d] == city_ids["Manchester"] for d in range(14, 18)]))  # days 15-18 (indices 14-17)
    
    # Frankfurt: show on day 5-6
    s.add(Or(itinerary[4] == city_ids["Frankfurt"], itinerary[5] == city_ids["Frankfurt"]))  # days 5 and 6 (indices 4,5)
    
    # Flight constraints: consecutive days in different cities must have a direct flight
    for d in range(days - 1):
        current_city = itinerary[d]
        next_city = itinerary[d + 1]
        for city1 in cities:
            for city2 in cities:
                if city1 != city2 and (city1, city2) not in direct_flights and (city2, city1) not in direct_flights:
                    s.add(Not(And(current_city == city_ids[city1], next_city == city_ids[city2])))
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        # Decode the itinerary
        itinerary_result = []
        city_list = list(cities.keys())
        for d in range(days):
            city_idx = m.evaluate(itinerary[d]).as_long()
            itinerary_result.append({"day": d + 1, "place": city_list[city_idx]})
        
        # Verify the counts
        counts = {city: 0 for city in cities}
        for entry in itinerary_result:
            counts[entry["place"]] += 1
        for city in cities:
            assert counts[city] == cities[city], f"City {city} has {counts[city]} days instead of {cities[city]}"
        
        # Verify Mykonos between days 10-12
        mykonos_days = [entry["day"] for entry in itinerary_result if entry["place"] == "Mykonos"]
        assert any(10 <= day <= 12 for day in mykonos_days), "Mykonos not visited between days 10-12"
        
        # Verify Manchester between days 15-18
        manchester_days = [entry["day"] for entry in itinerary_result if entry["place"] == "Manchester"]
        assert any(15 <= day <= 18 for day in manchester_days), "Manchester not visited between days 15-18"
        
        # Verify Frankfurt on day 5 or 6
        frankfurt_days = [entry["day"] for entry in itinerary_result if entry["place"] == "Frankfurt"]
        assert any(day == 5 or day == 6 for day in frankfurt_days), "Frankfurt not visited on day 5 or 6"
        
        # Verify flight connections
        for d in range(days - 1):
            current_place = itinerary_result[d]["place"]
            next_place = itinerary_result[d + 1]["place"]
            if current_place != next_place:
                assert (current_place, next_place) in direct_flights or (next_place, current_place) in direct_flights, f"No direct flight between {current_place} and {next_place} on day {d + 1}"
        
        # Prepare JSON output
        json_output = {"itinerary": [{"day": entry["day"], "place": entry["place"]} for entry in itinerary_result]}
        return json_output
    else:
        return {"error": "No valid itinerary found"}

# Execute the solver and print the result
result = solve_itinerary()
print(json.dumps(result, indent=2))