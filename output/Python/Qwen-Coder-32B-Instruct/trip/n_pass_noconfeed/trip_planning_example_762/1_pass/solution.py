import json

def calculate_itinerary():
    # Define the constraints
    constraints = {
        "Dublin": {"days": 3, "preferred_days": range(7, 10)},
        "Madrid": {"days": 2, "preferred_days": range(2, 4)},
        "Oslo": {"days": 3},
        "London": {"days": 2},
        "Vilnius": {"days": 3},
        "Berlin": {"days": 5, "preferred_days": range(3, 8)}
    }

    # Define the flight connections
    flights = {
        "London": ["Madrid", "Oslo", "Berlin", "Dublin"],
        "Madrid": ["London", "Oslo", "Berlin", "Dublin"],
        "Oslo": ["London", "Madrid", "Vilnius", "Berlin", "Dublin"],
        "Vilnius": ["Oslo", "Berlin"],
        "Berlin": ["London", "Madrid", "Oslo", "Vilnius", "Dublin"],
        "Dublin": ["London", "Madrid", "Oslo", "Berlin"]
    }

    # Initialize the itinerary
    itinerary = []
    current_day = 1
    current_city = None

    # Helper function to find the next city
    def find_next_city(current_city, remaining_days):
        for city, info in constraints.items():
            if city != current_city and (city not in [entry['place'] for entry in itinerary]):
                if len(itinerary) == 0 or city in flights[current_city]:
                    if 'preferred_days' in info:
                        start_day = max(current_day, min(info['preferred_days']))
                    else:
                        start_day = current_day
                    end_day = start_day + info['days'] - 1
                    if end_day <= 13:
                        return city, start_day, end_day
        return None, None, None

    # Build the itinerary
    while current_day <= 13:
        if not current_city:
            # Start with Berlin to meet the wedding constraint
            current_city = "Berlin"
            start_day = 1
            end_day = start_day + constraints[current_city]['days'] - 1
        else:
            current_city, start_day, end_day = find_next_city(current_city, 13 - current_day)
        
        if not current_city:
            break
        
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": current_city})
        current_day = end_day + 1

    # Output the itinerary as JSON
    return json.dumps({"itinerary": itinerary}, indent=4)

# Run the function and print the result
print(calculate_itinerary())