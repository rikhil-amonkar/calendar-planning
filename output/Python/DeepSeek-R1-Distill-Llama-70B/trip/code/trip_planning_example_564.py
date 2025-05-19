import json

# Define the cities and their required durations
cities = {
    'Istanbul': 2,
    'Rome': 3,
    'Seville': 4,
    'Naples': 7,
    'Santorini': 4
}

# Define flight connections
flight_connections = {
    'Rome': {'Santorini', 'Seville', 'Naples', 'Istanbul'},
    'Seville': {'Rome'},
    'Istanbul': {'Naples', 'Rome'},
    'Naples': {'Santorini', 'Rome', 'Istanbul'},
    'Santorini': set()
}

itinerary = []

# Start with Rome
current_day = 1
end_day = current_day + cities['Rome'] - 1
itinerary.append({'day_range': f'Day {current_day}-{end_day}', 'place': 'Rome'})
current_day = end_day + 1

# Fly to Seville
flight_day = 3
itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Rome', 'to': 'Seville'})

# Stay in Seville
start_day = flight_day
end_day = start_day + cities['Seville'] - 1
itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Seville'})
current_day = end_day + 1

# Fly to Istanbul
flight_day = 7
itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Seville', 'to': 'Istanbul'})

# Stay in Istanbul
start_day = flight_day
end_day = start_day + cities['Istanbul'] - 1
itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Istanbul'})
current_day = end_day + 1

# Fly to Naples
flight_day = 9
itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Istanbul', 'to': 'Naples'})

# Stay in Naples
start_day = flight_day
end_day = start_day + cities['Naples'] - 1
itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Naples'})
current_day = end_day + 1

# Fly to Santorini
flight_day = 16
itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Naples', 'to': 'Santorini'})

# Stay in Santorini
start_day = flight_day
end_day = start_day + cities['Santorini'] - 1
itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Santorini'})
current_day = end_day + 1

# Output the itinerary
print(json.dumps(itinerary))