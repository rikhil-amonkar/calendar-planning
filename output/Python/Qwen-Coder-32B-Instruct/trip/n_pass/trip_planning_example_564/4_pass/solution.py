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
    start_day = 1
    end_day = start_day + days_in_istanbul - 1
    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": "Istanbul"})
    
    # Fly to Naples on the next day and stay until the specified number of days
    start_day = end_day + 1
    end_day = start_day + days_in_naples - 1
    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": "Naples"})
    
    # Fly to Rome on the next day and stay until the specified number of days
    start_day = end_day + 1
    end_day = start_day + days_in_rome - 1
    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": "Rome"})
    
    # Fly to Seville on the next day and stay until the specified number of days
    start_day = end_day + 1
    end_day = start_day + days_in_seville - 1
    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": "Seville"})
    
    # Fly to Santorini on the next day and stay until the specified number of days
    start_day = end_day + 1
    end_day = start_day + days_in_santorini - 1
    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": "Santorini"})

    return itinerary

# Calculate the itinerary
itinerary = calculate_itinerary()

# Output the result as a JSON-formatted dictionary
print(json.dumps({"itinerary": itinerary}, indent=4))