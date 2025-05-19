import json

# Define the cities and their required durations
cities = {
    'Vilnius': 4,
    'Munich': 3,
    'Mykonos': 7
}

# Define flight connections
flight_connections = {
    'Vilnius': {'Munich'},
    'Munich': {'Mykonos'},
    'Mykonos': set()
}

itinerary = []

# Start with Vilnius
current_day = 1
end_day = current_day + cities['Vilnius'] - 1
itinerary.append({'day_range': f'Day {current_day}-{end_day}', 'place': 'Vilnius'})
current_day = end_day + 1

# Fly to Munich
flight_day = 4
itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Vilnius', 'to': 'Munich'})

# Stay in Munich
start_day = flight_day
end_day = start_day + cities['Munich'] - 1
itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Munich'})
current_day = end_day + 1

# Fly to Mykonos
flight_day = 6
itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Munich', 'to': 'Mykonos'})

# Stay in Mykonos
start_day = flight_day
end_day = start_day + cities['Mykonos'] - 1
itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Mykonos'})
current_day = end_day + 1

# Output the itinerary
print(json.dumps(itinerary))