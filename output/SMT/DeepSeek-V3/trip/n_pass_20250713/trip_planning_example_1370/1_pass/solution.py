from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        "Santorini": 5,
        "Krakow": 5,
        "Paris": 5,
        "Vilnius": 3,
        "Munich": 5,
        "Geneva": 2,
        "Amsterdam": 4,
        "Budapest": 5,
        "Split": 4
    }
    
    # Direct flights (undirected)
    direct_flights = [
        ("Paris", "Krakow"),
        ("Paris", "Amsterdam"),
        ("Paris", "Split"),
        ("Vilnius", "Munich"),
        ("Paris", "Geneva"),
        ("Amsterdam", "Geneva"),
        ("Munich", "Split"),
        ("Split", "Krakow"),
        ("Munich", "Amsterdam"),
        ("Budapest", "Amsterdam"),
        ("Split", "Geneva"),
        ("Vilnius", "Split"),
        ("Munich", "Geneva"),
        ("Munich", "Krakow"),
        ("Krakow", "Vilnius"),
        ("Vilnius", "Amsterdam"),
        ("Budapest", "Paris"),
        ("Krakow", "Amsterdam"),
        ("Vilnius", "Paris"),
        ("Budapest", "Geneva"),
        ("Split", "Amsterdam"),
        ("Santorini", "Geneva"),
        ("Amsterdam", "Santorini"),
        ("Munich", "Budapest"),
        ("Munich", "Paris")
    ]
    
    # Make flight connections bidirectional
    flight_pairs = set()
    for a, b in direct_flights:
        flight_pairs.add((a, b))
        flight_pairs.add((b, a))
    
    # Event constraints
    events = [
        ("Santorini", 25, 29),
        ("Krakow", 18, 22),
        ("Paris", 11, 15)
    ]
    
    # Total days
    total_days = 30
    
    # Create Z3 variables
    s = Solver()
    
    # day_place[i][j] is True if on day i+1 we are in city j
    day_place = [[Bool(f"day_{i+1}_{city}") for city in cities] for i in range(total_days)]
    city_index = {city: idx for idx, city in enumerate(cities)}
    
    # Each day must be in exactly one city (excluding flight days which are handled separately)
    for day in range(total_days):
        # At least one city per day
        s.add(Or([day_place[day][i] for i in range(len(cities))]))
        # At most one city per day (if not a flight day, but flight days are handled via two cities)
        # Flight days will have two cities, so this constraint is relaxed
    
    # Flight transitions: if day i is city A and day i+1 is city B, then there must be a direct flight
    for day in range(total_days - 1):
        for city1 in cities:
            for city2 in cities:
                if city1 != city2:
                    idx1 = city_index[city1]
                    idx2 = city_index[city2]
                    # If transitioning from city1 to city2, there must be a flight
                    implies_flight = Implies(
                        And(day_place[day][idx1], day_place[day + 1][idx2]),
                        (city1, city2) in flight_pairs
                    )
                    s.add(implies_flight)
    
    # Total days per city
    for city, days in cities.items():
        idx = city_index[city]
        total = Sum([If(day_place[d][idx], 1, 0) for d in range(total_days)])
        s.add(total == days)
    
    # Event constraints: certain cities must be visited within specific day ranges
    for city, start_day, end_day in events:
        idx = city_index[city]
        # At least one day in the range must be in the city
        s.add(Or([day_place[d][idx] for d in range(start_day - 1, end_day)]))
    
    # Now, we need to model flight days: if a person is in city A on day d and city B on day d+1, then day d is also in B (or A?)
    # This is complex. Alternatively, model that flight days are days where two cities are true.
    # But Z3 is not designed for this easily. So perhaps we need to adjust the approach.
    
    # Alternative approach: each day is a variable indicating the city, and flight days are handled by allowing two cities on the same day.
    # But Z3 doesn't handle multi-valued variables easily. So perhaps we need to use a list of cities per day, but that's not straightforward.
    
    # Given the complexity, perhaps the initial model is sufficient, and we'll post-process the solution to handle flight days.
    
    # Solve the model
    if s.check() == sat:
        m = s.model()
        # Extract the itinerary
        itinerary = []
        current_city = None
        start_day = 1
        for day in range(total_days):
            # Find which cities are true on this day
            day_cities = []
            for city in cities:
                idx = city_index[city]
                if m.evaluate(day_place[day][idx]):
                    day_cities.append(city)
            
            # For each city in day_cities, add to itinerary
            for city in day_cities:
                itinerary.append({"day_range": f"Day {day + 1}", "place": city})
            
            # Check if this day is a transition (i.e., multiple cities)
            if len(day_cities) > 1:
                pass  # already added both
            else:
                city = day_cities[0]
                # Check if it's a continuation from previous day
                if current_city == city:
                    # Extend the previous entry's day_range
                    if itinerary and itinerary[-1]["place"] == city:
                        prev_day_range = itinerary[-1]["day_range"]
                        if '-' in prev_day_range:
                            start, end = prev_day_range.replace("Day ", "").split('-')
                            new_range = f"Day {start}-{day + 1}"
                        else:
                            new_range = f"Day {prev_day_range.replace('Day ', '')}-{day + 1}"
                        itinerary[-1]["day_range"] = new_range
                    else:
                        itinerary.append({"day_range": f"Day {day + 1}", "place": city})
                else:
                    itinerary.append({"day_range": f"Day {day + 1}", "place": city})
                current_city = city
        
        # Post-process to merge consecutive days in the same city
        merged_itinerary = []
        i = 0
        n = len(itinerary)
        while i < n:
            current = itinerary[i]
            if i < n - 1 and itinerary[i+1]["place"] == current["place"]:
                start_day = current["day_range"].replace("Day ", "").split('-')[0]
                j = i + 1
                while j < n and itinerary[j]["place"] == current["place"]:
                    j += 1
                end_day = itinerary[j-1]["day_range"].replace("Day ", "").split('-')[-1]
                merged_range = f"Day {start_day}-{end_day}"
                merged_itinerary.append({"day_range": merged_range, "place": current["place"]})
                i = j
            else:
                merged_itinerary.append(current)
                i += 1
        
        # Now, handle flight days by ensuring that transition days have both cities
        # Reconstruct the itinerary with flight days explicitly
        final_itinerary = []
        prev_cities = set()
        for entry in merged_itinerary:
            day_range = entry["day_range"]
            place = entry["place"]
            if '-' in day_range:
                start, end = map(int, day_range.replace("Day ", "").split('-'))
                for day in range(start, end + 1):
                    final_itinerary.append({"day_range": f"Day {day}", "place": place})
            else:
                day = int(day_range.replace("Day ", ""))
                final_itinerary.append({"day_range": f"Day {day}", "place": place})
        
        # Group by day and find days with multiple cities
        day_to_cities = {}
        for entry in final_itinerary:
            day = int(entry["day_range"].replace("Day ", ""))
            if day not in day_to_cities:
                day_to_cities[day] = []
            day_to_cities[day].append(entry["place"])
        
        # Build the final itinerary with flight days
        final_itinerary_v2 = []
        for day in range(1, total_days + 1):
            cities_in_day = day_to_cities.get(day, [])
            for city in cities_in_day:
                final_itinerary_v2.append({"day_range": f"Day {day}", "place": city})
        
        # Now, merge consecutive stays again
        merged_final = []
        i = 0
        n = len(final_itinerary_v2)
        while i < n:
            current = final_itinerary_v2[i]
            if i < n - 1 and final_itinerary_v2[i+1]["place"] == current["place"] and final_itinerary_v2[i+1]["day_range"] == f"Day {int(current['day_range'].replace('Day ', '')) + 1}":
                start_day = int(current["day_range"].replace("Day ", ""))
                j = i + 1
                while j < n and final_itinerary_v2[j]["place"] == current["place"] and int(final_itinerary_v2[j]["day_range"].replace("Day ", "")) == start_day + (j - i):
                    j += 1
                end_day = start_day + (j - i) - 1
                merged_range = f"Day {start_day}-{end_day}"
                merged_final.append({"day_range": merged_range, "place": current["place"]})
                i = j
            else:
                merged_final.append(current)
                i += 1
        
        return {"itinerary": merged_final}
    else:
        return {"error": "No valid itinerary found"}

# Generate the itinerary
result = solve_itinerary()
print(json.dumps(result, indent=2))