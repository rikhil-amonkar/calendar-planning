import json

# Define the cities and their required durations
cities = {
    'Berlin': 3,
    'Barcelona': 2,
    'Lyon': 2,
    'Nice': 5,
    'Athens': 5,
    'Stockholm': 5,
    'Vilnius': 4
}

# Define flight connections
flight_connections = {
    'Berlin': {'Athens', 'Nice', 'Barcelona', 'Vilnius', 'Stockholm'},
    'Barcelona': {'Nice', 'Athens', 'Stockholm', 'Lyon'},
    'Lyon': {'Nice'},
    'Nice': {'Athens', 'Stockholm'},
    'Athens': {'Stockholm', 'Vilnius'},
    'Stockholm': {'Vilnius'},
    'Vilnius': set(),
    'Athens': {'Vilnius'}
}

itinerary = []

# Start with Berlin
current_day = 1
end_day = current_day + cities['Berlin'] - 1
itinerary.append({'day_range': f'Day {current_day}-{end_day}', 'place': 'Berlin'})
current_day = end_day + 1

# Fly to Barcelona
flight_day = 3
itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Berlin', 'to': 'Barcelona'})

# Stay in Barcelona
start_day = flight_day
end_day = start_day + cities['Barcelona'] - 1
itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Barcelona'})
current_day = end_day + 1

# Fly to Lyon
flight_day = 4
itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Barcelona', 'to': 'Lyon'})

# Stay in Lyon
start_day = flight_day
end_day = start_day + cities['Lyon'] - 1
itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Lyon'})
current_day = end_day + 1

# Fly to Nice
flight_day = 5
itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Lyon', 'to': 'Nice'})

# Stay in Nice
start_day = flight_day
end_day = start_day + cities['Nice'] - 1
itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Nice'})
current_day = end_day + 1

# Fly to Athens
flight_day = 9
itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Nice', 'to': 'Athens'})

# Stay in Athens
start_day = flight_day
end_day = start_day + cities['Athens'] - 1
itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Athens'})
current_day = end_day + 1

# Fly to Stockholm
flight_day = 13
itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Athens', 'to': 'Stockholm'})

# Stay in Stockholm
start_day = flight_day
end_day = start_day + cities['Stockholm'] - 1
itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Stockholm'})
current_day = end_day + 1

# Fly to Vilnius
flight_day = 17
itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Stockholm', 'to': 'Vilnius'})

# Stay in Vilnius
start_day = flight_day
end_day = start_day + cities['Vilnius'] - 1
itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Vilnius'})
current_day = end_day + 1

# Output the itinerary
print(json.dumps(itinerary))