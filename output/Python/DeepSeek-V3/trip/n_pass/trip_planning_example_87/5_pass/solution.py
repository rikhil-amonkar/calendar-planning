import json

def compute_itinerary():
    # Input parameters
    total_days = 7
    days_in_riga = 2
    days_in_amsterdam = 2
    days_in_mykonos = 3
    relatives_in_riga_between_day = (1, 2)  # Must visit Riga between these days
    
    # Direct flights available
    direct_flights = {
        'Amsterdam': ['Mykonos', 'Riga'],
        'Riga': ['Amsterdam'],
        'Mykonos': ['Amsterdam']
    }
    
    # Validate constraints
    total_requested_days = days_in_riga + days_in_amsterdam + days_in_mykonos
    if total_requested_days != total_days:
        raise ValueError("Invalid constraints: Total requested days do not match the trip duration.")
    
    # Validate Riga days match relative visit constraint
    if relatives_in_riga_between_day != (1, days_in_riga):
        raise ValueError("Riga visit must be on exactly days 1-2 to visit relatives")
    
    itinerary = []
    
    # Riga portion - fixed to days 1-2
    for day in range(1, days_in_riga + 1):
        itinerary.append({"day_range": f"Day {day}", "place": "Riga"})
    
    # Amsterdam portion
    for day in range(days_in_riga + 1, days_in_riga + days_in_amsterdam + 1):
        itinerary.append({"day_range": f"Day {day}", "place": "Amsterdam"})
    
    # Mykonos portion
    for day in range(days_in_riga + days_in_amsterdam + 1, total_days + 1):
        itinerary.append({"day_range": f"Day {day}", "place": "Mykonos"})
    
    # Verify days per city
    riga_days = sum(1 for entry in itinerary if entry["place"] == "Riga")
    amsterdam_days = sum(1 for entry in itinerary if entry["place"] == "Amsterdam")
    mykonos_days = sum(1 for entry in itinerary if entry["place"] == "Mykonos")
    
    if (riga_days != days_in_riga or amsterdam_days != days_in_amsterdam or mykonos_days != days_in_mykonos):
        raise ValueError("Invalid itinerary: Day counts do not match constraints.")
    
    # Verify flight connections are valid (only when changing cities)
    for i in range(len(itinerary)-1):
        current = itinerary[i]["place"]
        next_place = itinerary[i+1]["place"]
        if current != next_place:  # Only check flights when changing cities
            if next_place not in direct_flights.get(current, []):
                raise ValueError(f"Invalid transition: No direct flight from {current} to {next_place}")
    
    return {"itinerary": itinerary}

# Compute and output the itinerary
result = compute_itinerary()
print(json.dumps(result, indent=2))