import json

# Define the cities and their required durations
cities = {
    'Prague': 2,
    'Frankfurt': 3,
    'Naples': 4,
    'Helsinki': 4,
    'Lyon': 3
}

# Define flight connections
flight_connections = {
    'Prague': {'Lyon', 'Frankfurt', 'Helsinki'},
    'Frankfurt': {'Lyon', 'Naples', 'Helsinki'},
    'Helsinki': {'Naples', 'Frankfurt'},
    'Naples': {'Frankfurt'},
    'Lyon': set()
}

itinerary = []

# Start with Prague for the workshop
current_day = 1
end_day = current_day + cities['Prague'] - 1
itinerary.append({'day_range': f'Day {current_day}-{end_day}', 'place': 'Prague'})
current_day = end_day + 1

# Fly to Helsinki for the annual show
flight_day = 2
itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Prague', 'to': 'Helsinki'})

# Stay in Helsinki
start_day = flight_day
end_day = start_day + cities['Helsinki'] - 1
itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Helsinki'})
current_day = end_day + 1

# Fly to Frankfurt
flight_day = 6
itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Helsinki', 'to': 'Frankfurt'})

# Stay in Frankfurt
start_day = flight_day
end_day = start_day + cities['Frankfurt'] - 1
itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Frankfurt'})
current_day = end_day + 1

# Fly to Naples
flight_day = 9
itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Frankfurt', 'to': 'Naples'})

# Stay in Naples
start_day = flight_day
end_day = start_day + cities['Naples'] - 1
itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Naples'})
current_day = end_day + 1

# Fly to Lyon
flight_day = 13
itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Naples', 'to': 'Lyon'})

# Stay in Lyon
start_day = flight_day
end_day = start_day + cities['Lyon'] - 1
itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Lyon'})
current_day = end_day + 1

# Output the itinerary
print(json.dumps(itinerary))