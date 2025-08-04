import json

def calculate_itinerary():
    # Define the constraints
    total_days = 21
    days_in_reykjavik = 7
    days_in_riga = 2
    days_in_warsaw = 2
    days_in_istanbul = 5
    days_in_krakow = 5
    
    # Define the flight connections (not used in this simple itinerary generation)
    flights = {
        "Istanbul": ["Krakow", "Warsaw", "Riga"],
        "Krakow": ["Istanbul", "Warsaw"],
        "Warsaw": ["Krakow", "Reykjavik", "Istanbul", "Riga"],
        "Reykjavik": ["Warsaw"],
        "Riga": ["Istanbul", "Warsaw"]
    }
    
    # Initialize the itinerary
    itinerary = []
    
    # Start with Reykjavik
    current_day = 1
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_reykjavik - 1}", "place": "Reykjavik"})
    current_day += days_in_reykjavik
    
    # Move to Warsaw
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_warsaw - 1}", "place": "Warsaw"})
    current_day += days_in_warsaw
    
    # Move to Riga
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_riga - 1}", "place": "Riga"})
    current_day += days_in_riga
    
    # Move to Istanbul
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_istanbul - 1}", "place": "Istanbul"})
    current_day += days_in_istanbul
    
    # Move to Krakow
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_krakow - 1}", "place": "Krakow"})
    current_day += days_in_krakow
    
    # Return the itinerary as JSON
    return json.dumps({"itinerary": itinerary})

# Execute the function and print the result
print(calculate_itinerary())