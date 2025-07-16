import json

def compute_itinerary():
    # Input constraints
    total_days = 14
    city_days = {
        'Split': 4,
        'Vilnius': 3,
        'Santorini': 2,
        'Madrid': 5
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
    possible_orders = [
        ['Vilnius', 'Split', 'Madrid', 'Santorini'],
        ['Split', 'Vilnius', 'Madrid', 'Santorini']
    ]

    valid_order = None
    for order in possible_orders:
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
        days = city_days[city]
        end_day = current_day + days - 1
        
        if city == conference_city:
            # Ensure conference days match exactly
            if end_day != conference_days[1] or (end_day - days + 1) != conference_days[0]:
                return {"itinerary": []}
        
        itinerary.append({
            "day_range": f"Day {current_day}-{end_day}",
            "place": city
        })
        current_day = end_day + 1

    # Verify total days
    if current_day - 1 != total_days:
        return {"itinerary": []}

    return {"itinerary": itinerary}

# Execute and print the result
result = compute_itinerary()
print(json.dumps(result))