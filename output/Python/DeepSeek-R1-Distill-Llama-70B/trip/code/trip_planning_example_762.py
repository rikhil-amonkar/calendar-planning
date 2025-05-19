import json

def calculate_itinerary():
    # Define the cities and their required durations
    cities = {
        'Dublin': 3,
        'Madrid': 2,
        'Oslo': 3,
        'London': 2,
        'Vilnius': 3,
        'Berlin': 5
    }

    # Define fixed events with specific day ranges
    fixed_events = {
        'Madrid': (2, 3),
        'Berlin': (3, 7),
        'Dublin': (7, 9)
    }

    # Define flight connections
    flight_connections = {
        'London': ['Madrid', 'Oslo', 'Berlin', 'Dublin'],
        'Madrid': ['Oslo', 'Dublin', 'London', 'Berlin'],
        'Oslo': ['Vilnius', 'Madrid', 'London', 'Dublin', 'Berlin'],
        'Dublin': ['Oslo', 'London', 'Madrid', 'Berlin'],
        'Vilnius': ['Oslo', 'Berlin'],
        'Berlin': ['Vilnius', 'Oslo', 'Madrid', 'Dublin', 'London']
    }

    # Initialize itinerary
    itinerary = []
    current_day = 1
    remaining_cities = {city: days for city, days in cities.items() if city not in fixed_events}

    # Place fixed events first
    sorted_fixed_events = sorted(fixed_events.items(), key=lambda x: x[1][0])
    for city, (start, end) in sorted_fixed_events:
        itinerary.append({'day_range': f'Day {start}-{end}', 'place': city})
        current_day = end + 1

    # Fill remaining days with other cities
    for city in remaining_cities:
        if current_day > 13:
            break
        days_available = min(remaining_cities[city], 14 - current_day)
        if days_available <= 0:
            continue
        itinerary.append({'day_range': f'Day {current_day}-{current_day + days_available - 1}', 'place': city})
        current_day += days_available

    return itinerary

# Generate flight segments
itinerary = calculate_itinerary()
flight_segments = []
for i in range(len(itinerary)):
    if i == 0:
        prev_place = None
    else:
        prev_place = itinerary[i-1]['place']
    current_place = itinerary[i]['place']
    if prev_place is not None and prev_place != current_place:
        flight_segments.append({
            'flying': f'Day {itinerary[i]["day_range"].split("-")[0]}',
            'from': prev_place,
            'to': current_place
        })

# Combine day ranges and flight segments
final_itinerary = []
for segment in flight_segments:
    final_itinerary.append(segment)

for day_range in itinerary:
    final_itinerary.append(day_range)

# Output the result
print(json.dumps(final_itinerary, indent=2))