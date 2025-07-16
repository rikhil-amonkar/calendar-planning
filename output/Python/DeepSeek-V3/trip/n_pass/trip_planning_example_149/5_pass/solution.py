import json

def plan_trip():
    # Fixed parameters
    total_days = 10
    london_days = 3
    santorini_days = 5
    istanbul_days = 2
    conference_days = [5, 10]  # Must be on days 5 and 10
    
    # Direct flights
    direct_flights = {
        'Istanbul': ['London'],
        'London': ['Istanbul', 'Santorini'],
        'Santorini': ['London']
    }
    
    # Initialize itinerary
    itinerary = []
    
    # Solution approach:
    # - Need to have Santorini on both day 5 and day 10
    # - With only 5 Santorini days, this means we need two separate Santorini visits
    # - First visit: days 5-7 (3 days)
    # - Second visit: days 9-10 (2 days)
    # - This totals 5 Santorini days covering both conference days
    
    # Build the itinerary:
    # Days 1-3: London
    # Day 4: Istanbul
    # Days 5-7: Santorini (first visit, includes day 5 conference)
    # Day 8: London
    # Days 9-10: Santorini (second visit, includes day 10 conference)
    
    itinerary = [
        {"day": 1, "city": "London"},
        {"day": 2, "city": "London"},
        {"day": 3, "city": "London"},
        {"day": 4, "city": "Istanbul"},
        {"day": 5, "city": "Santorini"},  # Conference day 1
        {"day": 6, "city": "Santorini"},
        {"day": 7, "city": "Santorini"},  # Typo here - should be "Santorini"
        {"day": 8, "city": "London"},
        {"day": 9, "city": "Santorini"},  # Typo here - should be "Santorini"
        {"day": 10, "city": "Santorini"}  # Conference day 2
    ]
    
    # Fix the typos in city names
    for day in itinerary:
        if day["city"] == "Santorini":
            day["city"] = "Santorini"
    
    # Verify all constraints
    if len(itinerary) != total_days:
        raise ValueError("Itinerary length doesn't match total days")
    
    # Verify city days
    city_counts = {}
    for day in itinerary:
        city = day["city"]
        city_counts[city] = city_counts.get(city, 0) + 1
    
    if city_counts.get("London", 0) != london_days:
        raise ValueError(f"London days don't match: expected {london_days}, got {city_counts.get('London', 0)}")
    if city_counts.get("Santorini", 0) != santorini_days:
        raise ValueError(f"Santorini days don't match: expected {santorini_days}, got {city_counts.get('Santorini', 0)}")
    if city_counts.get("Istanbul", 0) != istanbul_days:
        raise ValueError(f"Istanbul days don't match: expected {istanbul_days}, got {city_counts.get('Istanbul', 0)}")
    
    # Verify conference days are in Santorini
    for day in conference_days:
        if itinerary[day-1]["city"] != "Santorini":
            raise ValueError(f"Day {day} not in Santorini for conference")
    
    # Verify flight connections
    for i in range(len(itinerary)-1):
        current = itinerary[i]["city"]
        next_city = itinerary[i+1]["city"]
        if next_city not in direct_flights.get(current, []):
            raise ValueError(f"No direct flight from {current} to {next_city}")
    
    return itinerary

# Execute and print the result as JSON
try:
    result = plan_trip()
    print(json.dumps(result, indent=2))
except ValueError as e:
    print(json.dumps({"error": str(e)}, indent=2))