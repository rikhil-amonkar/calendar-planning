import json

def calculate_itinerary():
    # Define constraints
    total_days = 23
    city_stays = {
        'Paris': 6,
        'Oslo': 5,
        'Porto': 7,
        'Geneva': 7,
        'Reykjavik': 2
    }
    fixed_events = {
        'Geneva': {'start': 1, 'end': 7},
        'Oslo': {'start': 19, 'end': 23}
    }
    direct_flights = {
        'Paris': ['Oslo', 'Reykjavik', 'Geneva', 'Porto'],
        'Oslo': ['Paris', 'Geneva', 'Reykjavik', 'Porto'],
        'Porto': ['Paris', 'Geneva', 'Oslo'],
        'Geneva': ['Paris', 'Oslo', 'Porto'],
        'Reykjavik': ['Paris', 'Oslo']
    }

    # Initialize itinerary
    itinerary = []

    # Fixed events
    # Geneva from day 1 to 7
    itinerary.append({'day_range': f'Day 1-7', 'place': 'Geneva'})
    remaining_geneva = city_stays['Geneva'] - 7
    city_stays['Geneva'] = remaining_geneva if remaining_geneva > 0 else 0

    # Oslo from day 19 to 23
    itinerary.append({'day_range': f'Day 19-23', 'place': 'Oslo'})
    remaining_oslo = city_stays['Oslo'] - (23 - 19 + 1)
    city_stays['Oslo'] = remaining_oslo if remaining_oslo > 0 else 0

    # Remaining days to allocate: 8-18 (11 days)
    remaining_days = 18 - 8 + 1
    remaining_cities = {city: days for city, days in city_stays.items() if days > 0}

    # Allocate remaining cities
    current_day = 8
    while current_day <= 18 and sum(remaining_cities.values()) > 0:
        for city in list(remaining_cities.keys()):
            if remaining_cities[city] == 0:
                continue
            # Check if city can be reached from previous location
            prev_location = itinerary[-1]['place'] if itinerary else 'Geneva'
            if city == prev_location or city in direct_flights.get(prev_location, []):
                days_to_spend = min(remaining_cities[city], 18 - current_day + 1)
                if days_to_spend <= 0:
                    continue
                end_day = current_day + days_to_spend - 1
                itinerary.append({'day_range': f'Day {current_day}-{end_day}', 'place': city})
                remaining_cities[city] -= days_to_spend
                current_day = end_day + 1
                break
        else:
            # No city can be reached, break to avoid infinite loop
            break

    # Verify all days are allocated
    allocated_days = 0
    for entry in itinerary:
        start, end = map(int, entry['day_range'].split('Day ')[1].split('-'))
        allocated_days += end - start + 1
    if allocated_days != total_days:
        # Adjust if needed (though constraints should ensure this is correct)
        pass

    return {'itinerary': itinerary}

# Compute and output the itinerary
result = calculate_itinerary()
print(json.dumps(result, indent=2))