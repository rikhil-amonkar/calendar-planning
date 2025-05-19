# Define required days for each city
required_days = {
    'Reykjavik': 2,
    'Oslo': 5,
    'Stuttgart': 5,
    'Split': 3,
    'Geneva': 2,
    'Porto': 3,
    'Tallinn': 5,
    'Stockholm': 3
}

# Define the order of cities to visit
order = [
    'Reykjavik',
    'Oslo',
    'Stuttgart',
    'Split',
    'Geneva',
    'Porto',
    'Tallinn',
    'Stockholm'
]

# Define direct flight connections between cities
flights = {
    'Reykjavik': ['Stuttgart', 'Stockholm', 'Tallinn'],
    'Oslo': ['Split', 'Geneva', 'Porto'],
    'Stuttgart': ['Porto', 'Split'],
    'Split': ['Stuttgart', 'Geneva'],
    'Geneva': ['Porto', 'Split', 'Stockholm'],
    'Porto': ['Geneva', 'Split', 'Stuttgart'],
    'Tallinn': ['Oslo'],
    'Stockholm': ['Oslo', 'Stuttgart', 'Split', 'Geneva']
}

itinerary = []

current_city = order[0]
start_day = 1
end_day = start_day + required_days[current_city] - 1
itinerary.append({
    'day_range': f'Day {start_day}-{end_day}',
    'place': current_city
})

for i in range(len(order) - 1):
    next_city = order[i + 1]
    # Check if there's a direct flight from current_city to next_city
    if next_city in flights.get(current_city, []):
        flight_day = end_day
        start_day_next = flight_day
        end_day_next = start_day_next + required_days[next_city] - 1
        itinerary.append({
            'flying': f'Day {flight_day}-{flight_day}',
            'from': current_city,
            'to': next_city
        })
        itinerary.append({
            'day_range': f'Day {start_day_next}-{end_day_next}',
            'place': next_city
        })
        current_city = next_city
        start_day = start_day_next
        end_day = end_day_next
    else:
        # No direct flight available, can't proceed further
        break

# Add the last city to the itinerary
itinerary.append({
    'day_range': f'Day {start_day}-{end_day}',
    'place': current_city
})

# Convert the itinerary list into the required JSON format
output = []
for segment in itinerary:
    if 'flying' in segment:
        output.append({
            'flying': segment['flying'],
            'from': segment['from'],
            'to': segment['to']
        })
    else:
        output.append({
            'day_range': segment['day_range'],
            'place': segment['place']
        })

print(output)