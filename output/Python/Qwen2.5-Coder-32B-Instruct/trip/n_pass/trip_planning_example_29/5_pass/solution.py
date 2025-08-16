import json

def calculate_itinerary():
    # Input constraints
    total_days = 10
    days_in_frankfurt = 3  # From Day 1 to Day 3
    days_in_krakow = 6     # From Day 4 to Day 9 (excluding Day 10 for Dubrovnik)
    days_in_dubrovnik = 2  # From Day 9 to Day 10
    
    # Initialize itinerary
    itinerary = []
    
    # Start in Frankfurt for the first 3 days
    itinerary.append({"day_range": f"Day 1-{days_in_frankfurt}", "place": "Frankfurt"})
    
    # Move to Krakow on day 4 and stay until day 9 (since Day 10 is for Dubrovnik)
    itinerary.append({"day_range": f"Day {days_in_frankfurt + 1}-{days_in_frankfurt + days_in_krakow}", "place": "Krakow"})
    
    # Move to Dubrovnik on day 10 and stay until day 10
    itinerary.append({"day_range": f"Day {total_days - days_in_dubrovnik + 1}-{total_days}", "place": "Dubrovnik"})
    
    return itinerary

# Calculate the itinerary
itinerary = calculate_itinerary()

# Output the result as JSON
output = {"itinerary": itinerary}
print(json.dumps(output))