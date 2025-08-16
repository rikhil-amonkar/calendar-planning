import json

def calculate_itinerary():
    # Input constraints
    total_days = 18
    days_in_krakow = 5
    days_in_frankfurt = 4
    days_in_oslo = 3
    days_in_dubrovnik = 5
    days_in_naples = 5
    
    # Fixed time slots
    oslo_visit_start = 16
    dubrovnik_friends_start = 5
    
    # Direct flight connections
    connections = {
        "Dubrovnik": ["Oslo", "Frankfurt", "Naples"],
        "Oslo": ["Dubrovnik", "Frankfurt", "Krakow", "Naples"],
        "Frankfurt": ["Dubrovnik", "Oslo", "Krakow"],
        "Krakow": ["Frankfurt", "Oslo"],
        "Naples": ["Oslo", "Dubrovnik", "Frankfurt"]
    }
    
    # Initialize itinerary
    itinerary = []
    current_day = 1
    
    # Start with Krakow for 5 days
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_krakow - 1}", "place": "Krakow"})
    current_day += days_in_krakow
    
    # Move to Frankfurt for 4 days
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_frankfurt - 1}", "place": "Frankfurt"})
    current_day += days_in_frankfurt
    
    # Move to Dubrovnik for 5 days, starting from day 5 to accommodate friends
    itinerary.append({"day_range": f"Day {dubrovnik_friends_start}-{dubrovnik_friends_start + days_in_dubrovnik - 1}", "place": "Dubrovnik"})
    current_day = dubrovnik_friends_start + days_in_dubrovnik
    
    # Move to Naples for 5 days
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_naples - 1}", "place": "Naples"})
    current_day += days_in_naples
    
    # Finally, move to Oslo for 3 days, starting from day 16 to visit relatives
    itinerary.append({"day_range": f"Day {oslo_visit_start}-{oslo_visit_start + days_in_oslo - 1}", "place": "Oslo"})
    
    return itinerary

# Calculate and print the itinerary in JSON format
itinerary = calculate_itinerary()
print(json.dumps({"itinerary": itinerary}))