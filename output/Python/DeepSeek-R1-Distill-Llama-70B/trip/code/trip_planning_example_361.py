import json

# Define the cities and their required durations
cities = {
    'Paris': 6,
    'Madrid': 7,
    'Bucharest': 2,
    'Seville': 3
}

# Define flight connections
flight_connections = {
    'Paris': {'Bucharest', 'Seville', 'Madrid'},
    'Madrid': {'Bucharest', 'Paris', 'Seville'},
    'Bucharest': {'Paris', 'Madrid'},
    'Seville': {'Paris', 'Madrid'}
}

itinerary = []

# Start with Madrid for the annual show
current_day = 1
end_day = current_day + cities['Madrid'] - 1
itinerary.append({'day_range': f'Day {current_day}-{end_day}', 'place': 'Madrid'})
current_day = end_day + 1

# Fly to Seville
flight_day = 7
itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Madrid', 'to': 'Seville'})

# Stay in Seville
start_day = flight_day
end_day = start_day + cities['Seville'] - 1
itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Seville'})
current_day = end_day + 1

# Fly to Paris
flight_day = 10
itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Seville', 'to': 'Paris'})

# Stay in Paris
start_day = flight_day
end_day = start_day + cities['Paris'] - 1
itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Paris'})
current_day = end_day + 1

# Fly to Bucharest
flight_day = 16
itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Paris', 'to': 'Bucharest'})

# Stay in Bucharest
start_day = flight_day
end_day = start_day + cities['Bucharest'] - 1
itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Bucharest'})
current_day = end_day + 1

# Output the itinerary
print(json.dumps(itinerary))