import json

def calculate_itinerary():
    # Define the constraints
    total_days = 16
    days_in_istanbul = 2
    days_in_naples = 5
    days_in_rome = 3
    days_in_seville = 4
    days_in_santorini = 2

    # Initialize the itinerary
    itinerary = []

    # Start in Istanbul on day 1 and stay for 2 days
    itinerary.append({"day_range": f"Day 1-2", "place": "Istanbul"})
    
    # Fly to Naples on day 3 and stay until day 7
    itinerary.append({"day_range": f"Day 3-7", "place": "Naples"})
    
    # Fly to Rome on day 8 and stay until day 10
    itinerary.append({"day_range": f"Day 8-10", "place": "Rome"})
    
    # Fly to Seville on day 11 and stay until day 14
    itinerary.append({"day_range": f"Day 11-14", "place": "Seville"})
    
    # Fly to Santorini on day 15 and stay until day 16
    itinerary.append({"day_range": f"Day 15-16", "place": "Santorini"})

    return itinerary

# Calculate the itinerary
itinerary = calculate_itinerary()

# Output the result as a JSON-formatted dictionary
print(json.dumps({"itinerary": itinerary}, indent=4))