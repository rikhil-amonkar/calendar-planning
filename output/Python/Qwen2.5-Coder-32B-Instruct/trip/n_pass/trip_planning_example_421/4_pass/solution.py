import json

def calculate_itinerary():
    # Define the constraints
    total_days = 20
    stay_nice = 5
    stay_krakow = 6
    stay_dublin = 7
    stay_lyon = 4
    stay_frankfurt = 2
    
    # Initialize the itinerary
    itinerary = []
    
    # Start in Nice for the first 5 days
    itinerary.append({"day_range": f"Day 1-{stay_nice}", "place": "Nice"})
    
    # From Nice, go to Frankfurt (day 6) and stay until day 6
    current_day = stay_nice + 1
    itinerary.append({"day_range": f"Day {current_day}-{current_day}", "place": "Frankfurt"})
    
    # From Frankfurt, go to Krakow (day 7) and stay for 6 days
    current_day += 1
    itinerary.append({"day_range": f"Day {current_day}-{current_day + stay_krakow - 1}", "place": "Krakow"})
    current_day += stay_krakow
    
    # From Krakow, go to Dublin (day 13) and stay for 7 days
    itinerary.append({"day_range": f"Day {current_day}-{current_day + stay_dublin - 1}", "place": "Dublin"})
    current_day += stay_dublin
    
    # From Dublin, go to Lyon (day 20) and stay for 4 days
    itinerary.append({"day_range": f"Day {current_day}-{current_day + stay_lyon - 1}", "place": "Lyon"})
    current_day += stay_lyon
    
    # From Lyon, go back to Frankfurt (day 19) to meet friends
    # Ensure the last two days are in Frankfurt
    if current_day <= total_days - stay_frankfurt:
        itinerary.append({"day_range": f"Day {total_days - stay_frankfurt + 1}-{total_days}", "place": "Frankfurt"})
    
    return itinerary

# Calculate the itinerary
itinerary = calculate_itinerary()

# Output the result as a JSON-formatted dictionary
output = {"itinerary": itinerary}
print(json.dumps(output, indent=4))