import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Dublin": {"days": 3, "preferred_range": (7, 9)},
        "Madrid": {"days": 2, "preferred_range": (2, 3)},
        "Oslo": {"days": 3},
        "London": {"days": 2},
        "Vilnius": {"days": 3},
        "Berlin": {"days": 5, "preferred_range": (3, 7)}
    }
    
    # Define the flight connections (not used in this specific problem, but kept for future use)
    flights = {
        "London": ["Madrid", "Oslo", "Berlin", "Dublin"],
        "Madrid": ["London", "Oslo", "Berlin", "Dublin"],
        "Oslo": ["London", "Madrid", "Berlin", "Vilnius"],
        "Berlin": ["London", "Madrid", "Oslo", "Vilnius", "Dublin"],
        "Dublin": ["London", "Madrid", "Berlin", "Oslo"],
        "Vilnius": ["Oslo", "Berlin"]
    }
    
    # Initialize the itinerary
    itinerary = []
    
    # Place Madrid first according to its preferred range
    madrid_start = 1
    itinerary.append({"day_range": f"Day {madrid_start}-{madrid_start + 1}", "place": "Madrid"})
    
    # Place Berlin next according to its preferred range
    berlin_start = 3
    itinerary.append({"day_range": f"Day {berlin_start}-{berlin_start + 4}", "place": "Berlin"})
    
    # Place Dublin next according to its preferred range
    dublin_start = 8
    itinerary.append({"day_range": f"Day {dublin_start}-{dublin_start + 2}", "place": "Dublin"})
    
    # Place London next
    london_start = 11
    itinerary.append({"day_range": f"Day {london_start}-{london_start + 1}", "place": "London"})
    
    # Place Vilnius last
    vilnius_start = 13
    itinerary.append({"day_range": f"Day {vilnius_start}-{vilnius_start}", "place": "Vilnius"})
    
    # Output the itinerary as JSON
    return {"itinerary": itinerary}

# Run the function and print the result
print(json.dumps(calculate_itinerary(), indent=4))