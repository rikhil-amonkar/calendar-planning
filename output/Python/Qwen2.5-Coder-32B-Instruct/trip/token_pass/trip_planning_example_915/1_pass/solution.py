import json

def plan_trip():
    # Define the constraints
    total_days = 26
    constraints = {
        "Bucharest": 3,
        "Venice": 5,
        "Prague": 4,
        "Frankfurt": 5,
        "Zurich": 5,
        "Florence": 5,
        "Tallinn": 5
    }
    mandatory_days = {
        "Venice": (22, 26),
        "Frankfurt": (12, 16),
        "Tallinn": (8, 12)
    }
    
    # Define available flights
    flights = [
        ("Prague", "Tallinn"),
        ("Prague", "Zurich"),
        ("Florence", "Prague"),
        ("Frankfurt", "Bucharest"),
        ("Frankfurt", "Venice"),
        ("Prague", "Bucharest"),
        ("Bucharest", "Zurich"),
        ("Tallinn", "Frankfurt"),
        ("Zurich", "Florence"),
        ("Frankfurt", "Zurich"),
        ("Zurich", "Venice"),
        ("Florence", "Frankfurt"),
        ("Prague", "Frankfurt"),
        ("Tallinn", "Zurich")
    ]
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    
    # Place mandatory events first
    def place_event(city, start_day, end_day):
        nonlocal current_day
        if start_day > current_day:
            # Add gap days if necessary
            itinerary.append({"day_range": f"Day {current_day}-{start_day-1}", "place": "Travel"})
            current_day = start_day
        itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": city})
        current_day = end_day + 1
    
    # Place events in the order of their mandatory days
    place_event("Tallinn", *mandatory_days["Tallinn"])
    place_event("Frankfurt", *mandatory_days["Frankfurt"])
    place_event("Venice", *mandatory_days["Venice"])
    
    # Remaining days to fill
    remaining_days = {
        "Bucharest": constraints["Bucharest"],
        "Prague": constraints["Prague"] - (current_day - mandatory_days["Frankfurt"][0] if current_day <= mandatory_days["Frankfurt"][1] else 0),
        "Zurich": constraints["Zurich"] - (current_day - mandatory_days["Tallinn"][0] if current_day <= mandatory_days["Tallinn"][1] else 0),
        "Florence": constraints["Florence"]
    }
    
    # Function to find a direct flight to a city
    def can_travel_to(current_city, target_city):
        return (current_city, target_city) in flights or (target_city, current_city) in flights
    
    # Fill in the remaining days
    current_city = "Tallinn"
    while current_day <= total_days:
        # Find a city to travel to next
        for city, days in remaining_days.items():
            if days > 0 and can_travel_to(current_city, city):
                # Travel to the city
                if current_city != city:
                    itinerary.append({"day_range": f"Day {current_day}-{current_day}", "place": city})
                    current_day += 1
                    current_city = city
                
                # Stay in the city
                stay_days = min(days, total_days - current_day + 1)
                itinerary.append({"day_range": f"Day {current_day}-{current_day+stay_days-1}", "place": city})
                current_day += stay_days
                remaining_days[city] -= stay_days
                break
    
    # Convert itinerary to JSON
    return json.dumps({"itinerary": itinerary}, indent=4)

# Run the function and print the result
print(plan_trip())