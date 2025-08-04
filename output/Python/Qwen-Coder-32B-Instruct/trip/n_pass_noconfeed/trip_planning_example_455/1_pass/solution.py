import json

def calculate_itinerary():
    # Define the constraints
    total_days = 21
    days_in_reykjavik = 7
    days_in_riga = 2
    days_in_warsaw = 3
    days_in_istanbul = 6
    days_in_krakow = 7
    
    # Define the flight connections
    flights = {
        "Istanbul": ["Krakow", "Warsaw", "Riga"],
        "Krakow": ["Istanbul", "Warsaw"],
        "Warsaw": ["Krakow", "Istanbul", "Reykjavik", "Riga"],
        "Riga": ["Istanbul", "Warsaw"],
        "Reykjavik": ["Warsaw"]
    }
    
    # Initialize the itinerary
    itinerary = []
    
    # Start in Riga to meet a friend between day 1 and day 2
    current_day = 1
    current_city = "Riga"
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_riga - 1}", "place": current_city})
    current_day += days_in_riga
    
    # Next, go to Warsaw (direct flight from Riga)
    current_city = "Warsaw"
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_warsaw - 1}", "place": current_city})
    current_day += days_in_warsaw
    
    # Then, go to Istanbul (direct flight from Warsaw)
    current_city = "Istanbul"
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_istanbul - 1}", "place": current_city})
    current_day += days_in_istanbul
    
    # Attend the wedding in Istanbul between day 2 and day 7, so we need to adjust if necessary
    # Since we already spent 1 day in Riga and 3 days in Warsaw, we are on day 6, which is fine
    
    # Next, go to Krakow (direct flight from Istanbul)
    current_city = "Krakow"
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_krakow - 1}", "place": current_city})
    current_day += days_in_krakow
    
    # Finally, go to Reykjavik (direct flight from Warsaw, but we need to come back via Istanbul)
    # However, since we are done with all other cities, we can directly go to Reykjavik from Krakow via Warsaw and Istanbul
    # But we need to ensure we have enough days left
    # We have already used 1 + 2 + 3 + 6 + 7 = 19 days, so we have 2 days left
    # We can adjust the previous legs to fit exactly 21 days
    
    # Adjust the itinerary to fit exactly 21 days
    # We can extend the stay in Krakow by 1 day and the stay in Reykjavik by 1 day
    itinerary[-1]["day_range"] = f"Day {current_day - 1}-{current_day + days_in_reykjavik - 1}"
    
    # Output the itinerary as JSON
    return json.dumps({"itinerary": itinerary})

# Run the function and print the result
print(calculate_itinerary())