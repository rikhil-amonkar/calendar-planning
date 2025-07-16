import json

def calculate_itinerary():
    # Input parameters
    total_days = 12
    naples_days = 3
    seville_days = 4
    milan_days = 5  # 3 + 5 + 4 = 12
    
    # Direct flight connections (graph representation)
    flight_network = {
        'Milan': ['Seville', 'Naples'],
        'Seville': ['Milan'],
        'Naples': ['Milan']
    }
    
    # Validate total days
    if naples_days + seville_days + milan_days != total_days:
        raise ValueError("Total days in cities do not match the trip duration.")
    
    # Create possible itineraries that satisfy flight connections
    possible_itineraries = [
        [('Naples', naples_days), ('Milan', milan_days), ('Seville', seville_days)],
        [('Milan', milan_days), ('Naples', naples_days), ('Seville', seville_days)],
        [('Milan', milan_days), ('Seville', seville_days), ('Naples', naples_days)],
        [('Seville', seville_days), ('Milan', milan_days), ('Naples', naples_days)]
    ]
    
    valid_itineraries = []
    for itinerary in possible_itineraries:
        valid = True
        for i in range(len(itinerary)-1):
            current_city = itinerary[i][0]
            next_city = itinerary[i+1][0]
            if next_city not in flight_network.get(current_city, []):
                valid = False
                break
        if valid:
            valid_itineraries.append(itinerary)
    
    if not valid_itineraries:
        raise ValueError("No valid itinerary found with given flight connections")
    
    # Select first valid itinerary (could implement preference logic here)
    selected_itinerary = valid_itineraries[0]
    
    # Generate day ranges
    current_day = 1
    formatted_itinerary = []
    for city, days in selected_itinerary:
        end_day = current_day + days - 1
        formatted_itinerary.append({
            "day_range": f"Day {current_day}-{end_day}",
            "place": city
        })
        current_day = end_day + 1
    
    return {"itinerary": formatted_itinerary}

# Execute the function and print the result as JSON
print(json.dumps(calculate_itinerary(), indent=2))