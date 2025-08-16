import json

def find_itinerary():
    # Define the constraints
    constraints = {
        "Vienna": 4,
        "Lyon": 3,
        "Edinburgh": 4,
        "Reykjavik": 5,
        "Stuttgart": 5,
        "Manchester": 2,
        "Split": 5,
        "Prague": 4
    }
    
    # Define the fixed events
    fixed_events = {
        "Edinburgh": (5, 8),
        "Split": (19, 23)
    }
    
    # Define the direct flight connections
    flights = {
        "Reykjavik": ["Stuttgart", "Split", "Vienna"],
        "Stuttgart": ["Reykjavik", "Vienna", "Edinburgh", "Manchester", "Prague", "Lyon", "Split"],
        "Vienna": ["Reykjavik", "Stuttgart", "Prague", "Manchester", "Lyon", "Split"],
        "Prague": ["Stuttgart", "Vienna", "Manchester", "Edinburgh", "Lyon", "Reykjavik", "Split"],
        "Manchester": ["Stuttgart", "Prague", "Vienna", "Split"],
        "Edinburgh": ["Stuttgart", "Prague", "Vienna"],
        "Lyon": ["Vienna", "Stuttgart", "Split", "Prague"],
        "Split": ["Reykjavik", "Stuttgart", "Manchester", "Prague", "Lyon", "Vienna"]
    }
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    current_city = None
    
    # Helper function to add a city to the itinerary
    def add_city(city, days):
        nonlocal current_day, current_city
        itinerary.append({"day_range": f"Day {current_day}-{current_day + days - 1}", "place": city})
        current_day += days
        current_city = city
    
    # Add fixed events first
    for city, (start, end) in fixed_events.items():
        if start == current_day:
            add_city(city, end - start + 1)
    
    # Add other cities
    for city, days in constraints.items():
        if city not in fixed_events:
            if current_city is None or city in flights[current_city]:
                add_city(city, days)
            else:
                # Find a reachable city
                for reachable_city in flights[current_city]:
                    if city in flights[reachable_city]:
                        add_city(reachable_city, 1)
                        add_city(city, days)
                        break
    
    # Ensure the total duration is 25 days
    if current_day < 26:
        # Add remaining days in the last city visited
        itinerary[-1]["day_range"] = f"Day {current_day}-Day 25"
    
    return itinerary

# Compute the itinerary
itinerary = find_itinerary()

# Output the result as JSON
print(json.dumps({"itinerary": itinerary}))