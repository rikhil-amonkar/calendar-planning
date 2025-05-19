import json

# Define the cities and their required durations
cities = {
    'Seville': 2,
    'Stuttgart': 7,
    'Porto': 3,
    'Madrid': 4
}

# Define flight connections
flight_connections = {
    'Seville': {'Porto'},
    'Stuttgart': {'Porto'},
    'Porto': {'Madrid'},
    'Madrid': {'Seville', 'Porto'}
}

itinerary = []

# Start with Madrid
current_day = 1
end_day = current_day + cities['Madrid'] - 1
itinerary.append({'day_range': f'Day {current_day}-{end_day}', 'place': 'Madrid'})
current_day = end_day + 1

# Fly to Seville
flight_day = 4
itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Madrid', 'to': 'Seville'})

# Stay in Seville
start_day = flight_day
end_day = start_day + cities['Seville'] - 1
itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Seville'})
current_day = end_day + 1

# Fly to Porto
flight_day = 6
itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Seville', 'to': 'Porto'})

# Stay in Porto
start_day = flight_day
end_day = start_day + cities['Porto'] - 1
itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Porto'})
current_day = end_day + 1

# Fly to Stuttgart
flight_day = 9
itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Porto', 'to': 'Stuttgart'})

# Stay in Stuttgart
start_day = flight_day
end_day = start_day + cities['Stuttgart'] - 1
itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Stuttgart'})
current_day = end_day + 1

# Output the itinerary
print(json.dumps(itinerary))