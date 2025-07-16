import json

def calculate_itinerary():
    # Adjusted days to spend in each city (total city days = 10, plus 2 travel days = 12)
    days_in_vilnius = 2  # Reduced from 3
    days_in_munich = 3
    days_in_mykonos = 5  # Reduced from 6
    
    # Direct flights available
    direct_flights = {
        'Vilnius': ['Munich'],
        'Munich': ['Vilnius', 'Mykonos'],
        'Mykonos': ['Munich']
    }
    
    # Determine the feasible sequence
    sequence = []
    # Try sequence Vilnius -> Munich -> Mykonos
    if 'Munich' in direct_flights['Vilnius'] and 'Mykonos' in direct_flights['Munich']:
        sequence = ['Vilnius', 'Munich', 'Mykonos']
    # Try sequence Mykonos -> Munich -> Vilnius
    elif 'Munich' in direct_flights['Mykonos'] and 'Vilnius' in direct_flights['Munich']:
        sequence = ['Mykonos', 'Munich', 'Vilnius']
    else:
        return {"error": "No valid sequence found with direct flights."}
    
    # Calculate total required days (city days + travel days)
    total_required_days = days_in_vilnius + days_in_munich + days_in_mykonos + 2
    if total_required_days != 12:
        return {"error": f"Total days including travel do not match 12. Current total: {total_required_days}"}
    
    # Build itinerary accounting for travel days
    itinerary = []
    current_day = 1
    
    # First city
    first_city = sequence[0]
    if first_city == 'Vilnius':
        end_day = current_day + days_in_vilnius - 1
        itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": "Vilnius"})
        current_day = end_day + 1  # Travel day to next city
    elif first_city == 'Munich':
        end_day = current_day + days_in_munich - 1
        itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": "Munich"})
        current_day = end_day + 1
    elif first_city == 'Mykonos':
        end_day = current_day + days_in_mykonos - 1
        itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": "Mykonos"})
        current_day = end_day + 1
    
    # Second city
    second_city = sequence[1]
    if second_city == 'Vilnius':
        end_day = current_day + days_in_vilnius - 1
        itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": "Vilnius"})
        current_day = end_day + 1
    elif second_city == 'Munich':
        end_day = current_day + days_in_munich - 1
        itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": "Munich"})
        current_day = end_day + 1
    elif second_city == 'Mykonos':
        end_day = current_day + days_in_mykonos - 1
        itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": "Mykonos"})
        current_day = end_day + 1
    
    # Third city
    third_city = sequence[2]
    if third_city == 'Vilnius':
        end_day = current_day + days_in_vilnius - 1
        itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": "Vilnius"})
    elif third_city == 'Munich':
        end_day = current_day + days_in_munich - 1
        itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": "Munich"})
    elif third_city == 'Mykonos':
        end_day = current_day + days_in_mykonos - 1
        itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": "Mykonos"})
    
    return {"itinerary": itinerary}

# Execute and print the result
result = calculate_itinerary()
print(json.dumps(result, indent=2))