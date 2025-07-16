import json

def compute_itinerary():
    # Input parameters
    total_days = 10
    days_in_krakow = 2
    wedding_day_start = 9
    days_in_dubrovnik = 7
    days_in_frankfurt = 3
    
    # Validate constraints
    total_requested_days = days_in_krakow + days_in_dubrovnik + days_in_frankfurt
    if total_requested_days != total_days:
        raise ValueError("Total days in cities do not match the trip duration")
    
    # Flight connections
    connections = {
        "Frankfurt": ["Krakow", "Dubrovnik"],
        "Krakow": ["Frankfurt"],
        "Dubrovnik": ["Frankfurt"]
    }
    
    # Determine the order of cities
    # Since wedding is in Krakow on day 9-10, Krakow must be last
    # Dubrovnik is 7 days, Frankfurt is 3, Krakow is 2
    # Possible sequences:
    # 1. Dubrovnik -> Frankfurt -> Krakow
    # 2. Frankfurt -> Dubrovnik -> Krakow
    
    # Check if sequence 1 is possible
    # Dubrovnik (1-7) -> Frankfurt (7-10) -> Krakow (10-12) - invalid (exceeds total days)
    # So sequence 1 is invalid
    
    # Check sequence 2:
    # Frankfurt (1-3) -> Dubrovnik (3-10) -> Krakow (10-12) - invalid (exceeds total days)
    # So need to adjust to have overlap on travel days
    
    # Alternative approach: account for travel days where you're in both cities
    # Since you're in both cities on travel day, the day counts overlap
    
    # Sequence: Frankfurt -> Dubrovnik -> Krakow
    # Frankfurt: days 1-3 (3 days)
    # Travel to Dubrovnik on day 3 (counts for both)
    # Dubrovnik: days 3-9 (7 days total: day 3 counts for both, days 4-9)
    # Travel to Krakow on day 9 (counts for both)
    # Krakow: days 9-10 (2 days: day 9 counts for both, day 10)
    
    itinerary = [
        {"day_range": "Day 1-3", "place": "Frankfurt"},
        {"day_range": "Day 3-9", "place": "Dubrovnik"},
        {"day_range": "Day 9-10", "place": "Krakow"}
    ]
    
    # Verify day counts
    frankfurt_days = 3  # days 1-3
    dubrovnik_days = (9 - 3) + 1  # days 3-9 (7 days)
    krakow_days = (10 - 9) + 1  # days 9-10 (2 days)
    
    if (frankfurt_days != days_in_frankfurt or
        dubrovnik_days != days_in_dubrovnik or
        krakow_days != days_in_krakow):
        raise ValueError("Computed itinerary does not satisfy day constraints")
    
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