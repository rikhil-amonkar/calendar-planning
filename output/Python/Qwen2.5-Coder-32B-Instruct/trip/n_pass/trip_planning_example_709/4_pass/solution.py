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

    # Ensure Porto fits within the meeting window (days 16 to 18)
    porto_start_day = constraints['port_meeting'][0]
    if porto_start_day + constraints['Porto'] - 1 > constraints['total_days']:
        raise ValueError("Cannot satisfy the meeting constraint in Porto within the total days limit.")

    # Add Porto stay
    current_city = "Porto"
    itinerary.append({"day_range": f"Day {porto_start_day}-{porto_start_day + constraints['Porto'] - 1}", "place": "Porto"})
    current_day = porto_start_day + constraints['Porto']

    # Add remaining days with Valencia and Dubrovnik
    remaining_days = constraints['total_days'] - current_day + 1
    if remaining_days > 0:
        # First, add Valencia stay if possible
        if remaining_days >= constraints['Valencia']:
            current_city = "Valencia"
            itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Valencia'] - 1}", "place": "Valencia"})
            current_day += constraints['Valencia']
            remaining_days -= constraints['Valencia']

        # Then, add Dubrovnik stay if possible
        if remaining_days >= constraints['Dubrovnik']:
            current_city = "Dubrovnik"
            itinerary.append({"day_range": f"Day {current_day}-{current_day + constraints['Dubrovnik'] - 1}", "place": "Dubrovnik"})
            current_day += constraints['Dubrovnik']
            remaining_days -= constraints['Dubrovnik']

    # Output the itinerary as JSON
    return json.dumps({"itinerary": itinerary}, indent=4)

# Run the function and print the result
print(calculate_itinerary())