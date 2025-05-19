import json

def calculate_itinerary():
    cities = {
        'Stockholm': (3, []),
        'Hamburg': (5, []),
        'Florence': (2, []),
        'Istanbul': (5, ['Day 25-29']),
        'Oslo': (5, []),
        'Vilnius': (5, []),
        'Santorini': (2, []),
        'Munich': (5, []),
        'Frankfurt': (4, []),
        'Krakow': (5, ['Day 5-9'])
    }

    direct_flights = {
        'Oslo': ['Stockholm', 'Istanbul', 'Krakow', 'Hamburg', 'Vilnius', 'Frankfurt'],
        'Krakow': ['Frankfurt', 'Istanbul', 'Vilnius', 'Munich', 'Stockholm'],
        'Munich': ['Stockholm', 'Hamburg', 'Istanbul', 'Florence', 'Krakow'],
        'Hamburg': ['Stockholm', 'Istanbul', 'Munich'],
        'Florence': ['Munich', 'Frankfurt'],
        'Istanbul': ['Oslo', 'Krakow', 'Stockholm', 'Munich', 'Frankfurt'],
        'Vilnius': ['Krakow', 'Istanbul', 'Frankfurt', 'Munich'],
        'Frankfurt': ['Krakow', 'Florence', 'Istanbul', 'Stockholm', 'Munich'],
        'Santorini': ['Stockholm', 'Oslo']
    }

    itinerary = []
    day_counter = 1
    total_days = 32

    # Add constraints
    for city, (days, constraints) in cities.items():
        if city == 'Istanbul' and 'Day 25-29' in constraints:
            itinerary.append({'day_range': f'Day {day_counter}-{day_counter+days-1}', 'place': city})
            day_counter += days
            continue
        if city == 'Krakow' and 'Day 5-9' in constraints:
            itinerary.append({'day_range': f'Day {day_counter}-{day_counter+days-1}', 'place': city})
            day_counter += days
            continue
        
        if day_counter + days <= total_days:
            itinerary.append({'day_range': f'Day {day_counter}-{day_counter+days-1}', 'place': city})
            day_counter += days

        # include transitions
        for next_city in direct_flights.get(city, []):
            if next_city in cities and day_counter < total_days:
                itinerary.append({'flying': f'Day {day_counter-1}-{day_counter-1}', 'from': city, 'to': next_city})
                # Break here to prevent adding too many transitions for the same city
                if next_city == 'Istanbul' and day_counter in range(25, 30):
                    break
        
    # Fill in any remaining days if needed (just to ensure we don't end before 32 days)
    while day_counter < total_days:
        itinerary.append({'day_range': f'Day {day_counter}-{day_counter}', 'place': 'Free Day'})
        day_counter += 1

    return json.dumps(itinerary, indent=4)

print(calculate_itinerary())