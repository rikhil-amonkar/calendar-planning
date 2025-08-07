from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Oslo": 2,
        "Helsinki": 2,
        "Edinburgh": 3,
        "Riga": 2,
        "Tallinn": 5,
        "Budapest": 5,
        "Vilnius": 5,
        "Porto": 5,
        "Geneva": 4
    }
    
    # Direct flights (undirected unless specified otherwise; but the problem states "direct flights" implying bidirectional)
    # Represented as a set of tuples
    direct_flights = {
        ("Porto", "Oslo"),
        ("Edinburgh", "Budapest"),
        ("Edinburgh", "Geneva"),
        ("Riga", "Tallinn"),
        ("Edinburgh", "Porto"),
        ("Vilnius", "Helsinki"),
        ("Tallinn", "Vilnius"),
        ("Riga", "Oslo"),
        ("Geneva", "Oslo"),
        ("Edinburgh", "Oslo"),
        ("Edinburgh", "Helsinki"),
        ("Vilnius", "Oslo"),
        ("Riga", "Helsinki"),
        ("Budapest", "Geneva"),
        ("Helsinki", "Budapest"),
        ("Helsinki", "Oslo"),
        ("Edinburgh", "Riga"),
        ("Tallinn", "Helsinki"),  # Assuming this is "Tallinn", "Helsinki"
        ("Geneva", "Porto"),
        ("Budapest", "Oslo"),
        ("Helsinki", "Geneva"),
        ("Riga", "Vilnius"),
        ("Tallinn", "Oslo")
    }
    
    # Make flights bidirectional
    flights = set()
    for a, b in direct_flights:
        flights.add((a, b))
        flights.add((b, a))
    direct_flights = flights
    
    # Create a Z3 solver instance
    s = Solver()
    
    # Days are 1..25
    days = 25
    
    # Create variables: assign each day to a city
    assignments = [Int(f"day_{i}") for i in range(1, days + 1)]
    
    # Map city names to numerical values
    city_ids = {city: idx for idx, city in enumerate(cities.keys())}
    id_to_city = {idx: city for city, idx in city_ids.items()}
    
    # Constraints: each day's assignment must be a valid city id
    for day in assignments:
        s.add(Or([day == city_ids[city] for city in cities]))
    
    # Constraints for the number of days in each city
    for city in cities:
        required_days = cities[city]
        s.add(Sum([If(assignments[i] == city_ids[city], 1, 0) for i in range(days)]) == required_days)
    
    # Flight constraints: consecutive days must be either the same city or connected by a direct flight
    for i in range(days - 1):
        current_city = assignments[i]
        next_city = assignments[i + 1]
        # Either stay in the same city or move to a connected city
        s.add(Or(
            current_city == next_city,
            *[And(current_city == city_ids[a], next_city == city_ids[b]) for a, b in direct_flights if a in city_ids and b in city_ids]
        ))
    
    # Special constraints:
    # 1. Wedding in Tallinn between day 4 and 8 (inclusive)
    s.add(Or([assignments[i] == city_ids["Tallinn"] for i in range(3, 8)]))  # days 4-8 (0-based: 3-7)
    
    # 2. Meet friend in Oslo between day 24 and 25 (inclusive)
    s.add(Or(assignments[23] == city_ids["Oslo"], assignments[24] == city_ids["Oslo"]))  # days 24-25 (0-based: 23-24)
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(days):
            city_id = model.evaluate(assignments[i]).as_long()
            city = id_to_city[city_id]
            itinerary.append({"day": i + 1, "place": city})
        
        # Verify the itinerary meets all constraints
        # (This is a sanity check; Z3 should have ensured it)
        city_days = {city: 0 for city in cities}
        for entry in itinerary:
            city_days[entry["place"]] += 1
        
        for city in cities:
            assert city_days[city] == cities[city], f"City {city} has {city_days[city]} days instead of {cities[city]}"
        
        # Check flight connections
        for i in range(len(itinerary) - 1):
            current = itinerary[i]["place"]
            next_ = itinerary[i + 1]["place"]
            if current != next_:
                assert (current, next_) in direct_flights or (next_, current) in direct_flights, f"No flight between {current} and {next_}"
        
        # Check wedding in Tallinn between day 4-8
        wedding_days = [entry["place"] for entry in itinerary if 4 <= entry["day"] <= 8]
        assert "Tallinn" in wedding_days, "Wedding in Tallinn not between days 4-8"
        
        # Check meeting friend in Oslo between day 24-25
        meeting_days = [entry["place"] for entry in itinerary if entry["day"] in [24, 25]]
        assert "Oslo" in meeting_days, "Meeting in Oslo not between days 24-25"
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Run the solver and print the result
result = solve_itinerary()
print(json.dumps(result, indent=2))