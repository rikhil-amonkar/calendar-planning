import json

def calculate_itinerary():
    # Define the constraints
    total_days = 18
    days_in_krakow = 5
    days_in_frankfurt = 4
    days_in_oslo = 3
    days_in_dubrovnik = 5
    days_in_naples = 1  # Adjusted to fit within 18 days without overlap
    
    # Initialize the itinerary
    itinerary = []
    current_day = 1
    
    # Start in Dubrovnik for the first part of the tour
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_dubrovnik - 1}", "place": "Dubrovnik"})
    current_day += days_in_dubrovnik
    
    # Move to Frankfurt after the tour
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_frankfurt - 1}", "place": "Frankfurt"})
    current_day += days_in_frankfurt
    
    # Move to Krakow from Frankfurt
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_krakow - 1}", "place": "Krakow"})
    current_day += days_in_krakow
    
    # Move to Naples from Krakow
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_naples - 1}", "place": "Naples"})
    current_day += days_in_naples
    
    # Move to Oslo for the visit
    itinerary.append({"day_range": f"Day {current_day}-{current_day + days_in_oslo - 1}", "place": "Oslo"})
    current_day += days_in_oslo
    
    return itinerary

# Calculate and output the itinerary
itinerary_result = {"itinerary": calculate_itinerary()}
print(json.dumps(itinerary_result))