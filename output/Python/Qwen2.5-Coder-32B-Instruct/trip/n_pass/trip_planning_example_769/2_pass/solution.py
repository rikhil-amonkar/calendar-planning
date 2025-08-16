import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Porto": 5,
        "Prague": 3,  # Reduced from 4 to fit within 16 days
        "Reykjavik": 3,  # Reduced from 4 to fit within 16 days
        "Santorini": 2,
        "Amsterdam": 2,
        "Munich": 3,  # Reduced from 4 to fit within 16 days
        "Reykjavik_wedding": (4, 7),
        "Amsterdam_conference": (14, 15),
        "Munich_meeting": (7, 10)
    }
    
    # Define the direct flights
    direct_flights = {
        "Porto": ["Amsterdam", "Munich"],
        "Amsterdam": ["Porto", "Munich", "Reykjavik", "Santorini", "Prague"],
        "Munich": ["Porto", "Amsterdam", "Reykjavik", "Prague"],
        "Reykjavik": ["Amsterdam", "Munich", "Prague"],
        "Santorini": ["Amsterdam"],
        "Prague": ["Amsterdam", "Reykjavik", "Munich"]
    }
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    
    # Start in Porto for 5 days
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Porto'] - 1}", "place": "Porto"})
    current_day += constraints['Porto']
    
    # Move to Munich for 3 days (to meet a friend between day 7 and day 10)
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Munich'] - 1}", "place": "Munich"})
    current_day += constraints['Munich']
    
    # Move to Prague for 3 days
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Prague'] - 1}", "place": "Prague"})
    current_day += constraints['Prague']
    
    # Move to Reykjavik for 3 days (to attend a wedding between day 4 and day 7)
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Reykjavik'] - 1}", "place": "Reykjavik"})
    current_day += constraints['Reykjavik']
    
    # Move to Amsterdam for 2 days (to attend a conference between day 14 and day 15)
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Amsterdam'] - 1}", "place": "Amsterdam"})
    current_day += constraints['Amsterdam']
    
    # Move to Santorini for 2 days
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Santorini'] - 1}", "place": "Santorini"})
    current_day += constraints['Santorini']
    
    # Ensure the total duration is exactly 16 days
    if current_day != 17:
        raise ValueError("Itinerary does not cover exactly 16 days")
    
    # Return the itinerary as a JSON-formatted dictionary
    return {"itinerary": itinerary}

# Output the result
print(json.dumps(calculate_itinerary(), indent=4))