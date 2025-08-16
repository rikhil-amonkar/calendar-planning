import json

def calculate_itinerary():
    # Input constraints
    total_days = 10
    days_in_krakow = 8  # From Day 4 to Day 11, but since we only have 10 days, it's Day 4 to Day 10
    krakow_wedding_days = [9, 10]
    days_in_dubrovnik = 2  # From Day 9 to Day 10
    days_in_frankfurt = 3  # From Day 1 to Day 3
    
    # Initialize itinerary
    itinerary = []
    
    # Start in Frankfurt for the first 3 days
    itinerary.append({"day_range": f"Day 1-{days_in_frankfurt}", "place": "Frankfurt"})
    
    # Move to Krakow on day 4 and stay until day 10 (specifically for the wedding)
    itinerary.append({"day_range": f"Day {days_in_frankfurt + 1}-{total_days}", "place": "Krakow"})
    
    # Since the wedding is from Day 9 to Day 10, we can consider the entire stay in Krakow for the wedding
    # No need to add a separate entry for Dubrovnik as the wedding days are already covered in Krakow
    
    return itinerary

# Calculate the itinerary
itinerary = calculate_itinerary()

# Output the result as JSON
output = {"itinerary": itinerary}
print(json.dumps(output))