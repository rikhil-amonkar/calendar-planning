from collections import defaultdict
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
    flight_graph = defaultdict(set)
    for a, b in direct_flights:
        flight_graph[a].add(b)
        flight_graph[b].add(a)
    
    # Fixed events
    fixed_events = [
        ("Santorini", 25, 29),
        ("Krakow", 18, 22),
        ("Paris", 11, 15)
    ]
    
    # Initialize itinerary
    itinerary = [None] * 30
    
    # Schedule fixed events first
    for city, start, end in fixed_events:
        for day in range(start-1, end):
            itinerary[day] = city
    
    # Assign remaining days
    remaining_cities = {city: days for city, days in cities.items()}
    for city, start, end in fixed_events:
        remaining_cities[city] -= (end - start + 1)
    
    # Helper function to find next city with available days
    def get_next_city(current_city):
        for city in remaining_cities:
            if remaining_cities[city] > 0 and (current_city is None or city in flight_graph[current_city]):
                return city
        return None
    
    # Fill in the itinerary
    current_city = None
    for day in range(30):
        if itinerary[day] is not None:
            current_city = itinerary[day]
            continue
        
        next_city = get_next_city(current_city)
        if next_city is None:
            # Try any city if no direct flight available
            for city in remaining_cities:
                if remaining_cities[city] > 0:
                    next_city = city
                    break
        
        if next_city is None:
            return {"error": "No valid itinerary found"}
        
        itinerary[day] = next_city
        remaining_cities[next_city] -= 1
        current_city = next_city
    
    # Verify all cities have correct days
    for city in cities:
        if itinerary.count(city) != cities[city]:
            return {"error": "Day count mismatch"}
    
    # Format the itinerary
    formatted_itinerary = []
    current_city = itinerary[0]
    start_day = 1
    for day in range(1, 30):
        if itinerary[day] != current_city:
            if start_day == day:
                formatted_itinerary.append({"day_range": f"Day {day}", "place": current_city})
            else:
                formatted_itinerary.append({"day_range": f"Day {start_day}-{day}", "place": current_city})
            formatted_itinerary.append({"day_range": f"Day {day+1}", "place": itinerary[day]})
            current_city = itinerary[day]
            start_day = day + 1
    formatted_itinerary.append({"day_range": f"Day {start_day}-30", "place": current_city})
    
    return {"itinerary": formatted_itinerary}

# Generate the itinerary
result = solve_itinerary()
print(json.dumps(result, indent=2))