import json

def calculate_itinerary():
    # Input constraints
    total_days = 10
    days_in_krakow = 2
    krakow_wedding_days = [9, 10]
    days_in_dubrovnik = 7
    days_in_frankfurt = 3
    
    # Initialize itinerary
    itinerary = []
    
    # Start in Frankfurt for the first 3 days
    itinerary.append({"day_range": f"Day 1-{days_in_frankfurt}", "place": "Frankfurt"})
    
    # Move to Krakow on day 3 and stay until day 10 (specifically for the wedding)
    itinerary.append({"day_range": f"Day {days_in_frankfurt}-Day {krakow_wedding_days[1]}", "place": "Krakow"})
    
    # Move to Dubrovnik on day 9 and stay until the end of the trip (Day 10)
    # Since we are already in Krakow on Day 9 and 10, we can directly move to Dubrovnik on Day 10
    itinerary.append({"day_range": f"Day {krakow_wedding_days[0]}-{total_days}", "place": "Dubrovnik"})
    
    return itinerary

# Calculate the itinerary
itinerary = calculate_itinerary()

# Output the result as JSON
output = {"itinerary": itinerary}
print(json.dumps(output))