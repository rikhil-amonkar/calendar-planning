import json

def calculate_itinerary():
    # Input parameters
    total_days = 17
    riga_days = 7
    budapest_days = 7
    paris_days = 4
    warsaw_days = 2
    
    # Constraints
    wedding_in_riga_start = 11
    wedding_in_riga_end = 17
    warsaw_show_start = 1
    warsaw_show_end = 2
    
    # Direct flights
    direct_flights = {
        'Warsaw': ['Budapest', 'Riga', 'Paris'],
        'Budapest': ['Warsaw', 'Paris'],
        'Paris': ['Budapest', 'Warsaw', 'Riga'],
        'Riga': ['Warsaw', 'Paris']
    }
    
    # Initialize itinerary
    itinerary = []
    
    # Warsaw show must be at the start (Day 1-2)
    itinerary.append({"day_range": f"Day {warsaw_show_start}-{warsaw_show_end}", "place": "Warsaw"})
    current_day = warsaw_show_end + 1
    
    # Next, we need to visit Budapest (7 days), Paris (4 days), and Riga (7 days with wedding constraints)
    # Possible orderings considering direct flights:
    # Warsaw -> Budapest -> Paris -> Riga
    # Warsaw -> Paris -> Budapest -> Riga
    # Warsaw -> Riga is not possible because wedding is later
    
    # Try Warsaw -> Budapest -> Paris -> Riga
    # Check if Budapest can be visited next
    if current_day + budapest_days - 1 <= wedding_in_riga_start - paris_days - 1:
        # Add Budapest
        budapest_end = current_day + budapest_days - 1
        itinerary.append({"day_range": f"Day {current_day}-{budapest_end}", "place": "Budapest"})
        current_day = budapest_end + 1
        
        # Add Paris
        paris_end = current_day + paris_days - 1
        itinerary.append({"day_range": f"Day {current_day}-{paris_end}", "place": "Paris"})
        current_day = paris_end + 1
        
        # Add Riga (must cover wedding days)
        riga_start = current_day
        riga_end = riga_start + riga_days - 1
        if riga_start <= wedding_in_riga_start and riga_end >= wedding_in_riga_end:
            itinerary.append({"day_range": f"Day {riga_start}-{riga_end}", "place": "Riga"})
            # Check if all days are covered
            if riga_end == total_days:
                return {"itinerary": itinerary}
    
    # Reset for next attempt
    itinerary = [{"day_range": f"Day {warsaw_show_start}-{warsaw_show_end}", "place": "Warsaw"}]
    current_day = warsaw_show_end + 1
    
    # Try Warsaw -> Paris -> Budapest -> Riga
    if current_day + paris_days - 1 <= wedding_in_riga_start - budapest_days - 1:
        # Add Paris
        paris_end = current_day + paris_days - 1
        itinerary.append({"day_range": f"Day {current_day}-{paris_end}", "place": "Paris"})
        current_day = paris_end + 1
        
        # Add Budapest
        budapest_end = current_day + budapest_days - 1
        itinerary.append({"day_range": f"Day {current_day}-{budapest_end}", "place": "Budapest"})
        current_day = budapest_end + 1
        
        # Add Riga
        riga_start = current_day
        riga_end = riga_start + riga_days - 1
        if riga_start <= wedding_in_riga_start and riga_end >= wedding_in_riga_end:
            itinerary.append({"day_range": f"Day {riga_start}-{riga_end}", "place": "Riga"})
            if riga_end == total_days:
                return {"itinerary": itinerary}
    
    # If no valid itinerary found (shouldn't happen with given constraints)
    return {"itinerary": []}

# Calculate and print the itinerary
result = calculate_itinerary()
print(json.dumps(result))