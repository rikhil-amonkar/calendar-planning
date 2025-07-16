import json

def calculate_itinerary():
    # Input constraints
    total_days = 12
    days_in_vilnius = 4
    days_in_munich = 3
    days_in_mykonos = 7
    
    # Direct flights available
    direct_flights = {
        'Vilnius': ['Munich'],
        'Munich': ['Vilnius', 'Mykonos'],
        'Mykonos': ['Munich']
    }
    
    # Validate if the given constraints are feasible with direct flights
    # We need to find a sequence where transitions are possible via direct flights
    # Given the constraints, the possible sequences are:
    # 1. Vilnius -> Munich -> Mykonos
    # 2. Mykonos -> Munich -> Vilnius
    
    # Check if the sum of days matches total_days
    if days_in_vilnius + days_in_munich + days_in_mykonos != total_days:
        return {"error": "Total days do not match the sum of days in each city."}
    
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
    
    # Build itinerary
    itinerary = []
    current_day = 1
    
    # First city
    first_city = sequence[0]
    if first_city == 'Vilnius':
        end_day = current_day + days_in_vilnius - 1
        itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": "Vilnius"})
        current_day = end_day
    elif first_city == 'Munich':
        end_day = current_day + days_in_munich - 1
        itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": "Munich"})
        current_day = end_day
    elif first_city == 'Mykonos':
        end_day = current_day + days_in_mykonos - 1
        itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": "Mykonos"})
        current_day = end_day
    
    # Transition day (counts for both cities)
    current_day += 1
    
    # Second city
    second_city = sequence[1]
    if second_city == 'Vilnius':
        end_day = current_day + days_in_vilnius - 1
        itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": "Vilnius"})
        current_day = end_day
    elif second_city == 'Munich':
        end_day = current_day + days_in_munich - 1
        itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": "Munich"})
        current_day = end_day
    elif second_city == 'Mykonos':
        end_day = current_day + days_in_mykonos - 1
        itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": "Mykonos"})
        current_day = end_day
    
    # Transition day (counts for both cities)
    current_day += 1
    
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