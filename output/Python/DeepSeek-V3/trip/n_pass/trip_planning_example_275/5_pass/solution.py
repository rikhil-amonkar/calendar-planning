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

    # Validate total days
    if sum(city_days.values()) != total_days:
        return {"itinerary": []}

    # Initialize itinerary
    itinerary = []

    # Determine possible orders that end with conference city
    possible_orders = [
        ['Vilnius', 'Split', 'Madrid', 'Santorini'],
        ['Split', 'Vilnius', 'Madrid', 'Santorini']
    ]

    valid_order = None
    for order in possible_orders:
        # Check flight connections
        valid_flights = True
        for i in range(len(order) - 1):
            if order[i+1] not in direct_flights.get(order[i], []):
                valid_flights = False
                break
        
        # Check if ends with conference city
        valid_conference = order[-1] == conference_city
        
        if valid_flights and valid_conference:
            valid_order = order
            break

    if not valid_order:
        return {"itinerary": []}

    # Assign days to cities ensuring conference days are correct
    current_day = 1
    for city in valid_order:
        days = city_days[city]
        end_day = current_day + days - 1
        
        # Special handling for conference city
        if city == conference_city:
            if current_day != conference_days[0] or end_day != conference_days[1]:
                return {"itinerary": []}
        
        itinerary.append({
            "day_range": f"Day {current_day}-{end_day}",
            "place": city
        })
        current_day = end_day + 1

    # Final validation
    if current_day - 1 != total_days:
        return {"itinerary": []}

    return {"itinerary": itinerary}

# Execute and print the result
result = compute_itinerary()
print(json.dumps(result))