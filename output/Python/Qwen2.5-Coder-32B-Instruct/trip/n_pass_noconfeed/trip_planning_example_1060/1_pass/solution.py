import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Stuttgart": (4, [4, 7]),
        "Istanbul": (4, [19, 22]),
        "Vilnius": (4, []),
        "Seville": (3, []),
        "Geneva": (5, []),
        "Valencia": (5, []),
        "Munich": (3, [13, 15]),
        "Reykjavik": (4, [1, 4])
    }
    
    # Define the flight connections
    flights = {
        "Geneva": ["Istanbul", "Munich", "Valencia"],
        "Reykjavik": ["Munich", "Stuttgart"],
        "Stuttgart": ["Valencia", "Istanbul", "Reykjavik"],
        "Munich": ["Reykjavik", "Stuttgart", "Geneva", "Istanbul", "Seville", "Vilnius"],
        "Istanbul": ["Stuttgart", "Geneva", "Munich", "Vilnius", "Valencia"],
        "Vilnius": ["Istanbul", "Munich"],
        "Seville": ["Valencia", "Munich"],
        "Valencia": ["Stuttgart", "Istanbul", "Geneva", "Munich", "Seville"]
    }
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    current_city = "Reykjavik"
    
    # Add initial fixed events
    itinerary.append({"day_range": f"Day {current_day}-{current_day + 3}", "place": current_city})
    current_day += 4
    
    # Function to add a stay to the itinerary
    def add_stay(city, duration):
        nonlocal current_day
        itinerary.append({"day_range": f"Day {current_day}-{current_day + duration - 1}", "place": city})
        current_day += duration
    
    # Add stays based on constraints
    for city, (duration, mandatory_days) in constraints.items():
        if city == "Reykjavik":
            continue
        if city == "Stuttgart":
            add_stay(city, duration)
            continue
        if city == "Istanbul":
            add_stay(city, duration)
            continue
        if city == "Vilnius":
            add_stay(city, duration)
            continue
        if city == "Seville":
            add_stay(city, duration)
            continue
        if city == "Geneva":
            add_stay(city, duration)
            continue
        if city == "Valencia":
            add_stay(city, duration)
            continue
        if city == "Munich":
            add_stay(city, duration)
            continue
    
    # Adjust for mandatory days
    for city, (duration, mandatory_days) in constraints.items():
        for day in mandatory_days:
            if day < current_day:
                continue
            while current_day < day:
                next_city = None
                for candidate_city in flights[current_city]:
                    if candidate_city not in [entry["place"] for entry in itinerary[-5:]]:
                        next_city = candidate_city
                        break
                if next_city:
                    itinerary.append({"day_range": f"Day {current_day}-{current_day}", "place": next_city})
                    current_city = next_city
                    current_day += 1
                else:
                    current_day += 1
            if current_day == day:
                itinerary.append({"day_range": f"Day {current_day}-{current_day}", "place": city})
                current_day += 1
    
    # Ensure all days are filled
    while current_day <= 25:
        next_city = None
        for candidate_city in flights[current_city]:
            if candidate_city not in [entry["place"] for entry in itinerary[-5:]]:
                next_city = candidate_city
                break
        if next_city:
            itinerary.append({"day_range": f"Day {current_day}-{current_day}", "place": next_city})
            current_city = next_city
            current_day += 1
        else:
            current_day += 1
    
    return itinerary

# Calculate and output the itinerary
itinerary = calculate_itinerary()
output = {"itinerary": itinerary}
print(json.dumps(output))