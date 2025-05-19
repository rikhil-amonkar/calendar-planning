import json

# Define the cities and their required durations
cities = {
    'Vienna': 2,
    'Nice': 2,
    'Stockholm': 5,
    'Split': 3
}

# Define flight connections
flight_connections = {
    'Vienna': {'Nice', 'Stockholm', 'Split'},
    'Nice': {'Stockholm'},
    'Stockholm': {'Split'},
    'Split': set()
}

itinerary = []

# Start with Vienna
current_day = 1
end_day = current_day + cities['Vienna'] - 1
itinerary.append({'day_range': f'Day {current_day}-{end_day}', 'place': 'Vienna'})
current_day = end_day + 1

# Fly to Nice
flight_day = 2
itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Vienna', 'to': 'Nice'})

# Stay in Nice
start_day = flight_day
end_day = start_day + cities['Nice'] - 1
itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Nice'})
current_day = end_day + 1

# Fly to Stockholm
flight_day = 4
itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Nice', 'to': 'Stockholm'})

# Stay in Stockholm
start_day = flight_day
end_day = start_day + cities['Stockholm'] - 1
itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Stockholm'})
current_day = end_day + 1

# Fly to Split
flight_day = 9
itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Stockholm', 'to': 'Split'})

# Stay in Split
start_day = flight_day
end_day = start_day + cities['Split'] - 1
itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Split'})
current_day = end_day + 1

# Output the itinerary
print(json.dumps(itinerary))