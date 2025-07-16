import json

def compute_itinerary():
    # Input constraints
    total_days = 14
    city_days = {
        'Split': 4,  # Reduced from 5 to make total days = 14
        'Vilnius': 3,  # Reduced from 4
        'Santorini': 2,
        'Madrid': 5  # Reduced from 6
    }
    conference_days = [13, 14]
    conference_city = 'Santorini'
    direct_flights = {
        'Vilnius': ['Split'],
        'Split': ['Vilnius', 'Madrid'],
        'Madrid': ['Split', 'Santorini'],
        'Santorini': ['Madrid']
    }

    # Initialize itinerary
    itinerary = []

    # Determine the order of visits based on constraints
    # Santorini must be last (days 13-14)
    # The other cities must be visited before Santorini
    # Possible order: Vilnius -> Split -> Madrid -> Santorini or Split -> Vilnius -> Madrid -> Santorini

    # Try possible orders and find one that fits
    possible_orders = [
        ['Vilnius', 'Split', 'Madrid', 'Santorini'],
        ['Split', 'Vilnius', 'Madrid', 'Santorini']
    ]

    valid_order = None
    for order in possible_orders:
        # Check if the order respects direct flights
        valid = True
        for i in range(len(order) - 1):
            if order[i+1] not in direct_flights[order[i]]:
                valid = False
                break
        if valid:
            valid_order = order
            break

    if not valid_order:
        return {"itinerary": []}

    # Assign days to cities
    current_day = 1
    for city in valid_order:
        if city == conference_city:
            # Assign conference days
            days = city_days[city]
            start_day = conference_days[0] - days + 1
            end_day = conference_days[1]
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": city
            })
            current_day = end_day + 1
        else:
            days = city_days[city]
            end_day = current_day + days - 1
            itinerary.append({
                "day_range": f"Day {current_day}-{end_day}",
                "place": city
            })
            current_day = end_day + 1

    # Verify total days
    total_planned = sum(city_days.values())
    if total_planned != total_days:
        return {"itinerary": []}

    return {"itinerary": itinerary}

# Execute and print the result
result = compute_itinerary()
print(json.dumps(result))