import json

def calculate_itinerary():
    # Input constraints
    total_days = 10
    days_in_krakow = 7  # From Day 4 to Day 10, excluding the last two days for Dubrovnik
    krakow_wedding_days = [9, 10]
    days_in_dubrovnik = 2  # From Day 9 to Day 10
    days_in_frankfurt = 3  # From Day 1 to Day 3
    
    # Initialize itinerary
    itinerary = []
    
    # Start in Frankfurt for the first 3 days
    itinerary.append({"day_range": f"Day 1-{days_in_frankfurt}", "place": "Frankfurt"})
    
    # Move to Krakow on day 4 and stay until day 8 (since Day 9 and Day 10 are for Dubrovnik)
    itinerary.append({"day_range": f"Day {days_in_frankfurt + 1}-{days_in_frankfurt + days_in_krakow}", "place": "Krakow"})
    
    # Move to Dubrovnik on day 9 and stay until day 10
    itinerary.append({"day_range": f"Day {days_in_frankfurt + days_in_krakow + 1}-{total_days}", "place": "Dubrovnik"})
    
    return itinerary

# Calculate the itinerary
itinerary = calculate_itinerary()

# Output the result as JSON
output = {"itinerary": itinerary}
print(json.dumps(output))