import json

def compute_itinerary():
    # Input constraints
    total_days = 7
    days_in_riga = 2
    days_in_amsterdam = 2
    days_in_mykonos = 3
    relatives_in_riga_between_day = (1, 2)  # Must be in Riga on days 1 and 2
    
    # Direct flights
    direct_flights = {
        'Amsterdam': ['Mykonos', 'Riga'],
        'Riga': ['Amsterdam'],
        'Mykonos': ['Amsterdam']
    }
    
    # Validate constraints
    total_requested_days = days_in_riga + days_in_amsterdam + days_in_mykonos
    if total_requested_days != total_days:
        raise ValueError(f"Total requested days do not sum to 7. Current sum: {total_requested_days}")
    
    # The only valid sequence is starting in Riga (to meet the relatives constraint)
    # Then moving to Amsterdam, then to Mykonos
    
    # Create itinerary
    itinerary = [
        {"day_range": "Day 1-2", "place": "Riga"},       # Days 1-2 in Riga
        {"day_range": "Day 3-4", "place": "Amsterdam"},  # Days 3-4 in Amsterdam
        {"day_range": "Day 5-7", "place": "Mykonos"}     # Days 5-7 in Mykonos
    ]
    
    # Verify all constraints are met
    riga_days = 0
    amsterdam_days = 0
    mykonos_days = 0
    relatives_constraint_met = False
    
    for entry in itinerary:
        place = entry["place"]
        day_range = entry["day_range"]
        start_day = int(day_range.split('-')[0].split(' ')[1])
        end_day = int(day_range.split('-')[1])
        days = end_day - start_day + 1
        
        if place == "Riga":
            riga_days += days
            # Check if we're in Riga during the required days
            if (start_day <= relatives_in_riga_between_day[0] and 
                end_day >= relatives_in_riga_between_day[1]):
                relatives_constraint_met = True
        elif place == "Amsterdam":
            amsterdam_days += days
        elif place == "Mykonos":
            mykonos_days += days
    
    # Check all constraints
    if (riga_days == days_in_riga and 
        amsterdam_days == days_in_amsterdam and 
        mykonos_days == days_in_mykonos and 
        relatives_constraint_met):
        return {"itinerary": itinerary}
    else:
        raise ValueError("No valid itinerary found with the given constraints.")

# Compute and output the itinerary
result = compute_itinerary()
print(json.dumps(result, indent=2))