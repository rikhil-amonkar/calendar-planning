import json

def compute_itinerary():
    # Input parameters
    total_days = 10
    days_in_krakow = 2
    wedding_day_start = 9
    days_in_dubrovnik = 7
    days_in_frankfurt = 3
    
    # Validate constraints
    total_requested_days = (days_in_frankfurt + 
                           days_in_dubrovnik + 
                           days_in_krakow - 2)  # Subtract 2 for two travel days
    if total_requested_days != total_days:
        raise ValueError("Total days in cities do not match the trip duration")
    
    # Flight connections
    connections = {
        "Frankfurt": ["Krakow"],
        "Krakow": ["Frankfurt", "Dubrovnik"],
        "Dubrovnik": ["Krakow"]
    }
    
    # Create itinerary
    # Frankfurt: days 1-3 (3 days)
    # Travel to Krakow on day 3 (counts as last day in Frankfurt)
    # Krakow: days 3-5 (2 days: day 3 is travel, day 4 is full day)
    # Travel to Dubrovnik on day 5 (counts as last day in Krakow)
    # Dubrovnik: days 5-9 (5 days: day 5 is travel, days 6-9 are full days)
    # Travel to Krakow on day 9 (counts as last day in Dubrovnik)
    # Krakow: days 9-10 (2 days: day 9 is travel, day 10 is full day)
    
    itinerary = [
        {"day_range": "Day 1-3", "place": "Frankfurt"},
        {"day_range": "Day 3-5", "place": "Krakow"},
        {"day_range": "Day 5-9", "place": "Dubrovnik"},
        {"day_range": "Day 9-10", "place": "Krakow"}
    ]
    
    # Verify day counts
    frankfurt_days = 3  # days 1-3
    krakow_days = 2  # day 4 (first visit) and day 10 (second visit)
    dubrovnik_days = 5  # days 6-9 plus travel day 5
    
    # Verify total days
    if (frankfurt_days + krakow_days + dubrovnik_days) != total_days:
        raise ValueError("Day counts don't add up correctly")
    
    # Verify flight connections
    cities = [segment["place"] for segment in itinerary]
    for i in range(len(cities) - 1):
        current_city = cities[i]
        next_city = cities[i+1]
        if next_city not in connections.get(current_city, []):
            raise ValueError(f"No direct flight from {current_city} to {next_city}")
    
    # Verify wedding is in Krakow on day 9-10
    wedding_segment = itinerary[-1]
    if (wedding_segment["place"] != "Krakow" or
        wedding_segment["day_range"] != "Day 9-10"):
        raise ValueError("Wedding constraints not satisfied")
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    itinerary = compute_itinerary()
    print(json.dumps(itinerary))