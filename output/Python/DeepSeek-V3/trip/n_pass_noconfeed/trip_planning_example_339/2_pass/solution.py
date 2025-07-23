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
    
    # Possible orderings considering direct flights:
    # 1. Warsaw -> Budapest -> Paris -> Riga
    # 2. Warsaw -> Paris -> Budapest -> Riga
    
    # Try Option 1: Warsaw -> Budapest -> Paris -> Riga
    # Add Budapest
    budapest_end = current_day + budapest_days - 1
    if budapest_end > total_days:
        pass  # Skip if it exceeds total days
    else:
        temp_itinerary = itinerary.copy()
        temp_itinerary.append({"day_range": f"Day {current_day}-{budapest_end}", "place": "Budapest"})
        next_day = budapest_end + 1
        
        # Add Paris
        paris_end = next_day + paris_days - 1
        if paris_end > total_days:
            pass  # Skip if it exceeds total days
        else:
            temp_itinerary.append({"day_range": f"Day {next_day}-{paris_end}", "place": "Paris"})
            riga_start = paris_end + 1
            riga_end = riga_start + riga_days - 1
            
            # Check if Riga stay includes wedding days and fits in total days
            if (riga_start <= wedding_in_riga_start and 
                riga_end >= wedding_in_riga_end and 
                riga_end <= total_days):
                temp_itinerary.append({"day_range": f"Day {riga_start}-{riga_end}", "place": "Riga"})
                return {"itinerary": temp_itinerary}
    
    # Try Option 2: Warsaw -> Paris -> Budapest -> Riga
    # Reset variables
    current_day = warsaw_show_end + 1
    
    # Add Paris
    paris_end = current_day + paris_days - 1
    if paris_end > total_days:
        pass  # Skip if it exceeds total days
    else:
        temp_itinerary = itinerary.copy()
        temp_itinerary.append({"day_range": f"Day {current_day}-{paris_end}", "place": "Paris"})
        next_day = paris_end + 1
        
        # Add Budapest
        budapest_end = next_day + budapest_days - 1
        if budapest_end > total_days:
            pass  # Skip if it exceeds total days
        else:
            temp_itinerary.append({"day_range": f"Day {next_day}-{budapest_end}", "place": "Budapest"})
            riga_start = budapest_end + 1
            riga_end = riga_start + riga_days - 1
            
            # Check if Riga stay includes wedding days and fits in total days
            if (riga_start <= wedding_in_riga_start and 
                riga_end >= wedding_in_riga_end and 
                riga_end <= total_days):
                temp_itinerary.append({"day_range": f"Day {riga_start}-{riga_end}", "place": "Riga"})
                return {"itinerary": temp_itinerary}
    
    # If no valid itinerary found (shouldn't happen with given constraints)
    return {"itinerary": []}

# Calculate and print the itinerary
result = calculate_itinerary()
print(json.dumps(result, indent=2))