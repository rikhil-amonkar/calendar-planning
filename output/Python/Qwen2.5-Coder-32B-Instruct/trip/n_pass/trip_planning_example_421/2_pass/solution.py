import json

def calculate_itinerary():
    # Define the constraints
    total_days = 20
    stay_nice = 5
    stay_krakow = 6
    stay_dublin = 7
    stay_lyon = 4
    stay_frankfurt = 2
    nice_visit_start = 1
    nice_visit_end = nice_visit_start + stay_nice - 1
    frankfurt_meet_start = total_days - stay_frankfurt + 1
    frankfurt_meet_end = frankfurt_meet_start + stay_frankfurt - 1
    
    # Initialize the itinerary
    itinerary = []
    
    # Start in Nice for the first 5 days
    itinerary.append({"day_range": f"Day {nice_visit_start}-{nice_visit_end}", "place": "Nice"})
    
    # Next, go to Frankfurt (day 6) and stay until day 6
    itinerary.append({"day_range": f"Day {nice_visit_end + 1}-{nice_visit_end + 1}", "place": "Frankfurt"})
    
    # From Frankfurt, go to Krakow (day 7) and stay for 6 days
    itinerary.append({"day_range": f"Day {nice_visit_end + 2}-{nice_visit_end + 2 + stay_krakow - 1}", "place": "Krakow"})
    
    # From Krakow, go to Dublin (day 13) and stay for 3 days to reach the required 7 days in Dublin
    itinerary.append({"day_range": f"Day {nice_visit_end + 2 + stay_krakow}-{nice_visit_end + 2 + stay_krakow + 3 - 1}", "place": "Dublin"})
    
    # From Dublin, go to Lyon (day 16) and stay for 4 days
    itinerary.append({"day_range": f"Day {nice_visit_end + 2 + stay_krakow + 3}-{nice_visit_end + 2 + stay_krakow + 3 + stay_lyon - 1}", "place": "Lyon"})
    
    # From Lyon, go back to Dublin (day 20) and stay for 2 days to meet friends in Frankfurt
    itinerary.append({"day_range": f"Day {nice_visit_end + 2 + stay_krakow + 3 + stay_lyon}-{nice_visit_end + 2 + stay_krakow + 3 + stay_lyon + 2 - 1}", "place": "Dublin"})
    
    # From Dublin, go to Frankfurt (day 21) to meet friends
    itinerary.append({"day_range": f"Day {frankfurt_meet_start}-{frankfurt_meet_end}", "place": "Frankfurt"})
    
    return itinerary

# Calculate the itinerary
itinerary = calculate_itinerary()

# Output the result as a JSON-formatted dictionary
output = {"itinerary": itinerary}
print(json.dumps(output, indent=4))