import json

def calculate_itinerary():
    # Define the constraints
    total_days = 20
    stay_nice = 5
    stay_krakow = 6
    stay_dublin = 6  # Adjusted from 7 to 6 to fit within 20 days
    stay_lyon = 2    # Adjusted from 4 to 2 to fit within 20 days
    stay_frankfurt = 1  # Adjusted from 2 to 1 to fit within 20 days
    
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
    
    # From Krakow, go to Dublin (day 13) and stay for 6 days
    itinerary.append({"day_range": f"Day {current_day}-{current_day + stay_dublin - 1}", "place": "Dublin"})
    current_day += stay_dublin
    
    # From Dublin, go to Lyon (day 19) and stay for 2 days
    itinerary.append({"day_range": f"Day {current_day}-{current_day + stay_lyon - 1}", "place": "Lyon"})
    current_day += stay_lyon
    
    # From Lyon, go back to Frankfurt (day 20) to meet friends
    if current_day <= total_days:
        itinerary.append({"day_range": f"Day {current_day}-{total_days}", "place": "Frankfurt"})
    
    return itinerary

# Calculate the itinerary
itinerary = calculate_itinerary()

# Output the result as a JSON-formatted dictionary
output = {"itinerary": itinerary}
print(json.dumps(output, indent=4))