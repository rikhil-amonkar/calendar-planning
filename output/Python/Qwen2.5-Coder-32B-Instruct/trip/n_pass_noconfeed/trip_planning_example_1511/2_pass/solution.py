import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Venice": (3, None),
        "Reykjavik": (2, None),
        "Munich": (3, (4, 6)),
        "Santorini": (3, (8, 10)),
        "Manchester": (3, None),
        "Porto": (3, None),
        "Bucharest": (5, None),
        "Tallinn": (4, None),
        "Valencia": (2, (14, 15)),
        "Vienna": (5, None)
    }
    
    # Define the direct flights
    direct_flights = {
        "Bucharest": ["Manchester", "Valencia", "Vienna"],
        "Munich": ["Venice", "Porto", "Manchester", "Reyjavik", "Vienna", "Bucharest", "Valencia", "Tallinn", "Santorini"],
        "Santorini": ["Venice", "Manchester", "Vienna", "Bucharest"],
        "Vienna": ["Reykjavik", "Venice", "Santorini", "Manchester", "Porto", "Valencia", "Bucharest", "Munich"],
        "Venice": ["Munich", "Santorini", "Manchester", "Vienna"],
        "Manchester": ["Santorini", "Vienna", "Porto", "Munich", "Bucharest"],
        "Porto": ["Vienna", "Manchester", "Valencia", "Munich"],
        "Valencia": ["Vienna", "Manchester", "Porto", "Bucharest", "Munich"],
        "Reykjavik": ["Vienna", "Munich"],
        "Tallinn": ["Munich"]
    }
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    
    # Helper function to add a stay to the itinerary
    def add_stay(city, start_day, end_day):
        nonlocal current_day
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
        current_day = end_day + 1
    
    # Add fixed stays first
    add_stay("Munich", 4, 6)  # Annual show in Munich
    add_stay("Santorini", 8, 10)  # Visit relatives in Santorini
    add_stay("Valencia", 14, 15)  # Workshop in Valencia
    
    # Remaining cities to visit
    remaining_cities = set(constraints.keys()) - {"Munich", "Santorini", "Valencia"}
    
    # Start from a city with a direct flight to Munich
    current_city = "Vienna"
    add_stay(current_city, 1, 3)
    
    # Plan the rest of the itinerary
    while remaining_cities:
        next_city = None
        for city in remaining_cities:
            if current_city in direct_flights[city]:
                next_city = city
                break
        
        if not next_city:
            # If no direct flight is found, try to find a city with a direct flight to any city in the itinerary
            for city in remaining_cities:
                for visited_city in [item["place"] for item in itinerary]:
                    if visited_city in direct_flights[city]:
                        next_city = city
                        break
                if next_city:
                    break
        
        if not next_city:
            raise ValueError("No valid itinerary found")
        
        days_to_stay, _ = constraints[next_city]
        add_stay(next_city, current_day, current_day + days_to_stay - 1)
        remaining_cities.remove(next_city)
        current_city = next_city
    
    # Ensure the total duration is 24 days
    if current_day != 25:
        raise ValueError("Itinerary does not match the required duration")
    
    return {"itinerary": itinerary}

# Calculate and print the itinerary
print(json.dumps(calculate_itinerary(), indent=4))