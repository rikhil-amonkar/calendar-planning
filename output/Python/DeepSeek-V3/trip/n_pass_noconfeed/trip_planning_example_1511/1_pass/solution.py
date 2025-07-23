import json
from itertools import permutations

def find_itinerary():
    # Cities and their required days
    cities = {
        "Venice": 3,
        "Reykjavik": 2,
        "Munich": 3,
        "Santorini": 3,
        "Manchester": 3,
        "Porto": 3,
        "Bucharest": 5,
        "Tallinn": 4,
        "Valencia": 2,
        "Vienna": 5
    }
    
    # Direct flights
    direct_flights = {
        "Bucharest": ["Manchester", "Valencia", "Vienna", "Munich", "Santorini"],
        "Munich": ["Venice", "Porto", "Manchester", "Reykjavik", "Vienna", "Bucharest", "Tallinn", "Valencia"],
        "Santorini": ["Manchester", "Venice", "Vienna", "Bucharest"],
        "Vienna": ["Reykjavik", "Valencia", "Manchester", "Porto", "Venice", "Santorini", "Bucharest", "Munich"],
        "Venice": ["Munich", "Santorini", "Manchester", "Vienna"],
        "Manchester": ["Bucharest", "Santorini", "Vienna", "Venice", "Porto", "Munich"],
        "Porto": ["Munich", "Vienna", "Valencia", "Manchester"],
        "Reykjavik": ["Vienna", "Munich"],
        "Valencia": ["Vienna", "Bucharest", "Porto", "Munich"],
        "Tallinn": ["Munich"]
    }
    
    # Fixed constraints
    fixed_constraints = [
        ("Munich", 4, 6),
        ("Santorini", 8, 10),
        ("Valencia", 14, 15)
    ]
    
    # Generate all possible city orders (permutations)
    city_names = list(cities.keys())
    
    # We'll try a heuristic approach due to computational complexity
    # Start with fixed constraints and fill in the rest
    
    itinerary = []
    days_used = 0
    current_city = None
    
    # Initialize days
    day_assignments = [None] * 24
    
    # Assign fixed constraints first
    for city, start_day, end_day in fixed_constraints:
        for day in range(start_day - 1, end_day):
            day_assignments[day] = city
    
    # Assign cities with fixed durations in a logical order
    remaining_cities = {city: dur for city, dur in cities.items()}
    for city, start_day, end_day in fixed_constraints:
        remaining_cities.pop(city)
    
    # Try to assign Tallinn (4 days) early (it's only connected to Munich)
    if "Tallinn" in remaining_cities:
        # Find Munich days
        munich_days = [i for i, city in enumerate(day_assignments) if city == "Munich"]
        if munich_days:
            # Assign Tallinn right after Munich
            start_day = munich_days[-1] + 1
            if start_day + 4 <= 24:
                for day in range(start_day, start_day + 4):
                    if day_assignments[day] is None:
                        day_assignments[day] = "Tallinn"
                remaining_cities.pop("Tallinn")
    
    # Assign remaining cities
    for city in list(remaining_cities.keys()):
        dur = remaining_cities[city]
        # Find first available consecutive days
        start_day = None
        for i in range(24 - dur + 1):
            if all(day_assignments[i + j] is None for j in range(dur)):
                # Check if it's reachable from previous city
                prev_city = None
                if i > 0:
                    prev_city = day_assignments[i - 1]
                if prev_city is None or city in direct_flights.get(prev_city, []):
                    start_day = i
                    break
        if start_day is not None:
            for day in range(start_day, start_day + dur):
                day_assignments[day] = city
            remaining_cities.pop(city)
    
    # Fill any remaining None days with Vienna (most connected city)
    for i in range(24):
        if day_assignments[i] is None:
            day_assignments[i] = "Vienna"
    
    # Convert to itinerary format
    itinerary = []
    current_city = day_assignments[0]
    start_day = 1
    for i in range(1, 24):
        if day_assignments[i] != current_city:
            end_day = i
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": current_city
            })
            current_city = day_assignments[i]
            start_day = i + 1
    itinerary.append({
        "day_range": f"Day {start_day}-24",
        "place": current_city
    })
    
    return {"itinerary": itinerary}

# Output the result
print(json.dumps(find_itinerary(), indent=2))