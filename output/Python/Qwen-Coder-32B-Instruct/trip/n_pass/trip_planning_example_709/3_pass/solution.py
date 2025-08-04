import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Helsinki": 4,
        "Valencia": 5,
        "Dubrovnik": 4,
        "Porto": 3,
        "Prague": 3,
        "Reykjavik": 4,
        "total_days": 18,
        "port_meeting": (16, 18)
    }

    # Define the flight connections
    connections = {
        "Helsinki": ["Prague", "Reykjavik", "Dubrovnik"],
        "Prague": ["Helsinki", "Valencia"],
        "Valencia": ["Prague", "Porto"],
        "Porto": ["Valencia"],
        "Reykjavik": ["Helsinki", "Prague"],
        "Dubrovnik": ["Helsinki"]
    }

    # Initialize the itinerary
    itinerary = []
    current_day = 1
    current_city = "Helsinki"

    # Add Helsinki stay
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Helsinki'] - 1}", "place": "Helsinki"})
    current_day += constraints['Helsinki']

    # Add Reykjavik stay
    current_city = "Reykjavik"
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Reykjavik'] - 1}", "place": "Reykjavik"})
    current_day += constraints['Reykjavik']

    # Add Prague stay
    current_city = "Prague"
    itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Prague'] - 1}", "place": "Prague"})
    current_day += constraints['Prague']

    # Adjust current_day to ensure Porto can fit within the meeting window (days 16 to 18)
    # Porto needs 3 days, so it should start on day 16 at the latest
    porto_start_day = max(current_day, constraints['port_meeting'][0] - constraints['Porto'] + 1)
    if porto_start_day + constraints['Porto'] - 1 > constraints['port_meeting'][1]:
        raise ValueError("Cannot satisfy the meeting constraint in Porto.")
    
    # If the calculated porto_start_day is after the meeting window, we need to backtrack
    if porto_start_day > constraints['port_meeting'][1] - constraints['Porto'] + 1:
        # Adjust the previous stays to make room for Porto in the meeting window
        # We will try to reduce the stay in Prague if possible
        if current_day - constraints['Prague'] >= constraints['port_meeting'][0] - constraints['Porto'] + 1:
            # Reduce the stay in Prague
            prague_end_day = constraints['port_meeting'][0] - constraints['Porto'] + 1
            prague_stay = prague_end_day - (current_day - constraints['Prague'])
            if prague_stay < 1:
                raise ValueError("Cannot satisfy the meeting constraint in Porto even after adjusting previous stays.")
            
            # Update the itinerary for Prague
            itinerary[-1]["day_range"] = f"Day {current_day - constraints['Prague']}-{prague_end_day - 1}"
            current_day = prague_end_day
    
    # Add Porto stay
    current_city = "Porto"
    itinerary.append({"day_range": f"Day {porto_start_day}-{porto_start_day + constraints['Porto'] - 1}", "place": "Porto"})
    current_day = porto_start_day + constraints['Porto']

    # Add Valencia stay (if needed)
    if current_day <= constraints['total_days'] - constraints['Valencia']:
        current_city = "Valencia"
        itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Valencia'] - 1}", "place": "Valencia"})
        current_day += constraints['Valencia']

    # Add Dubrovnik stay (if needed)
    if current_day <= constraints['total_days'] - constraints['Dubrovnik']:
        current_city = "Dubrovnik"
        itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Dubrovnik'] - 1}", "place": "Dubrovnik"})
        current_day += constraints['Dubrovnik']

    # Output the itinerary as JSON
    return json.dumps({"itinerary": itinerary}, indent=4)

# Run the function and print the result
print(calculate_itinerary())