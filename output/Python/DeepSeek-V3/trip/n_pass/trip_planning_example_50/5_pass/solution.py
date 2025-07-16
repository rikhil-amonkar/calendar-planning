import json

def calculate_itinerary():
    # Days to spend in each city (8 days total in cities)
    days_in_vilnius = 2
    days_in_munich = 3
    days_in_mykonos = 3
    
    # 3 travel days (Vilnius->Munich, Munich->Mykonos, and return)
    travel_days = 3
    
    # Total days = 8 city days + 3 travel days + 1 buffer day = 12
    buffer_day = 1
    
    # Direct flights available
    direct_flights = {
        'Vilnius': ['Munich'],
        'Munich': ['Vilnius', 'Mykonos'],
        'Mykonos': ['Munich']
    }
    
    # Determine the feasible sequence
    sequence = []
    if 'Munich' in direct_flights['Vilnius'] and 'Mykonos' in direct_flights['Munich']:
        sequence = ['Vilnius', 'Munich', 'Mykonos']
    else:
        return {"error": "No valid sequence found with direct flights."}
    
    # Build itinerary with explicit travel days
    itinerary = []
    current_day = 1
    
    # Vilnius (Days 1-2)
    end_day = current_day + days_in_vilnius - 1
    itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": "Vilnius"})
    current_day = end_day + 1
    
    # Travel to Munich (Day 3)
    itinerary.append({"day_range": f"Day {current_day}", "place": "Travel to Munich"})
    current_day += 1
    
    # Munich (Days 4-6)
    end_day = current_day + days_in_munich - 1
    itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": "Munich"})
    current_day = end_day + 1
    
    # Travel to Mykonos (Day 7)
    itinerary.append({"day_range": f"Day {current_day}", "place": "Travel to Mykonos"})
    current_day += 1
    
    # Mykonos (Days 8-10)
    end_day = current_day + days_in_mykonos - 1
    itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": "Mykonos"})
    current_day = end_day + 1
    
    # Return travel day (Day 11)
    itinerary.append({"day_range": f"Day {current_day}", "place": "Return travel"})
    current_day += 1
    
    # Buffer day (Day 12)
    itinerary.append({"day_range": f"Day {current_day}", "place": "Flexible day"})
    
    return {"itinerary": itinerary}

# Execute and print the result
result = calculate_itinerary()
print(json.dumps(result, indent=2))