import json

def calculate_itinerary():
    # Define the constraints
    total_days = 21
    days_in_reykjavik = 7
    days_in_riga = 2
    days_in_warsaw = 2
    days_in_istanbul = 5
    days_in_krakow = 5
    
    # Define the flight connections
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
    
    # Move to Warsaw (from Reykjavik)
    if "Warsaw" in flights["Reykjavik"]:
        itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_warsaw - 1}", "place": "Warsaw"})
        current_day += days_in_warsaw
    else:
        raise ValueError("No direct flight from Reykjavik to Warsaw")
    
    # Move to Riga (from Warsaw)
    if "Riga" in flights["Warsaw"]:
        itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_riga - 1}", "place": "Riga"})
        current_day += days_in_riga
    else:
        raise ValueError("No direct flight from Warsaw to Riga")
    
    # Move to Istanbul (from Riga)
    if "Istanbul" in flights["Riga"]:
        itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_istanbul - 1}", "place": "Istanbul"})
        current_day += days_in_istanbul
    else:
        raise ValueError("No direct flight from Riga to Istanbul")
    
    # Move to Krakow (from Istanbul)
    if "Krakow" in flights["Istanbul"]:
        itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_krakow - 1}", "place": "Krakow"})
        current_day += days_in_krakow
    else:
        raise ValueError("No direct flight from Istanbul to Krakow")
    
    # Ensure the total days constraint is met
    if current_day != total_days + 1:
        raise ValueError(f"Total days in itinerary do not match the required {total_days} days.")
    
    # Return the itinerary as JSON
    return json.dumps({"itinerary": itinerary})

# Execute the function and print the result
print(calculate_itinerary())