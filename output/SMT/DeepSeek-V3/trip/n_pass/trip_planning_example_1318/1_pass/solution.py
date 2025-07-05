from z3 import *

def solve_itinerary():
    # Cities to visit
    cities = ["Oslo", "Helsinki", "Edinburgh", "Riga", "Tallinn", "Budapest", "Vilnius", "Porto", "Geneva"]
    
    # Direct flights as tuples (from, to)
    direct_flights = [
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
        ("Tallinn", "Helsinki"),
        ("Geneva", "Porto"),
        ("Budapest", "Oslo"),
        ("Helsinki", "Geneva"),
        ("Riga", "Vilnius"),
        ("Tallinn", "Oslo")
    ]
    
    # Bidirectional flights
    flight_pairs = set()
    for a, b in direct_flights:
        flight_pairs.add((a, b))
        flight_pairs.add((b, a))
    
    # Days: 1 to 25
    days = 25
    
    # Create Z3 variables: day_i is the city on day i (1-based)
    day_vars = [Int(f"day_{i}") for i in range(1, days + 1)]
    
    # Solver
    s = Solver()
    
    # Each day_var must be an index representing a city (0 to 8)
    city_map = {city: idx for idx, city in enumerate(cities)}
    inv_city_map = {idx: city for idx, city in enumerate(cities)}
    
    for day in day_vars:
        s.add(day >= 0, day < len(cities))
    
    # Constraints for durations
    # Oslo: 2 days (including flight days)
    # Helsinki: 2 days
    # Edinburgh: 3 days
    # Riga: 2 days
    # Tallinn: 5 days (wedding between day 4-8)
    # Budapest: 5 days
    # Vilnius: 5 days
    # Porto: 5 days
    # Geneva: 4 days
    
    # Count occurrences of each city
    city_counts = []
    for city_idx in range(len(cities)):
        count = Sum([If(day == city_idx, 1, 0) for day in day_vars])
        city_counts.append(count)
    
    s.add(city_counts[city_map["Oslo"]] == 2)
    s.add(city_counts[city_map["Helsinki"]] == 2)
    s.add(city_counts[city_map["Edinburgh"]] == 3)
    s.add(city_counts[city_map["Riga"]] == 2)
    s.add(city_counts[city_map["Tallinn"]] == 5)
    s.add(city_counts[city_map["Budapest"]] == 5)
    s.add(city_counts[city_map["Vilnius"]] == 5)
    s.add(city_counts[city_map["Porto"]] == 5)
    s.add(city_counts[city_map["Geneva"]] == 4)
    
    # Wedding in Tallinn between day 4 and 8: at least one day in Tallinn in days 4-8
    wedding_days = [day_vars[i] for i in range(3, 8)]  # days 4-8 (0-based 3 to 7)
    s.add(Or([day == city_map["Tallinn"] for day in wedding_days]))
    
    # Meet friend in Oslo between day 24 and 25: at least one of day 24 or 25 is Oslo
    s.add(Or(day_vars[23] == city_map["Oslo"], day_vars[24] == city_map["Oslo"]))
    
    # Flight transitions: consecutive days must be same city or connected by direct flight
    for i in range(days - 1):
        current_city = day_vars[i]
        next_city = day_vars[i + 1]
        # Either same city or connected by flight
        same_city = (current_city == next_city)
        flight_connection = Or([And(current_city == city_map[a], next_city == city_map[b]) for a, b in flight_pairs])
        s.add(Or(same_city, flight_connection))
    
    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        current_place = None
        start_day = 1
        
        # Helper to add entries to itinerary
        def add_entry(place, start, end):
            if start == end:
                itinerary.append({"day_range": f"Day {start}", "place": place})
            else:
                itinerary.append({"day_range": f"Day {start}-{end}", "place": place})
        
        # Process each day
        for day in range(1, days + 1):
            city_idx = model.evaluate(day_vars[day - 1]).as_long()
            city = inv_city_map[city_idx]
            if current_place is None:
                current_place = city
                start_day = day
            elif city != current_place:
                # Add the previous stay
                add_entry(current_place, start_day, day - 1)
                # Add the flight day (previous city)
                itinerary.append({"day_range": f"Day {day}", "place": current_place})
                # Add the flight day (new city)
                itinerary.append({"day_range": f"Day {day}", "place": city})
                current_place = city
                start_day = day
        # Add the last stay
        add_entry(current_place, start_day, days)
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found."}

# Generate and print the itinerary
itinerary = solve_itinerary()
print(itinerary)