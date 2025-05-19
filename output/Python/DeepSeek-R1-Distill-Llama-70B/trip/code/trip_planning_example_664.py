import json

# Define the cities and their required durations
cities = {
    'Tallinn': 2,
    'Bucharest': 4,
    'Seville': 5,
    'Stockholm': 5,
    'Munich': 5,
    'Milan': 2
}

# Define flight connections
flight_connections = {
    'Milan': {'Stockholm'},
    'Munich': {'Stockholm', 'Seville', 'Milan', 'Tallinn'},
    'Bucharest': {'Munich'},
    'Seville': {'Milan'},
    'Stockholm': {'Tallinn'},
    'Tallinn': set()
}

itinerary = []

# Start with Bucharest
current_day = 1
end_day = current_day + cities['Bucharest'] - 1
itinerary.append({'day_range': f'Day {current_day}-{end_day}', 'place': 'Bucharest'})
current_day = end_day + 1

# Fly to Munich
flight_day = 4
itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Bucharest', 'to': 'Munich'})

# Stay in Munich
start_day = flight_day
end_day = start_day + cities['Munich'] - 1
itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Munich'})
current_day = end_day + 1

# Fly to Seville
flight_day = 8
itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Munich', 'to': 'Seville'})

# Stay in Seville
start_day = flight_day
end_day = start_day + cities['Seville'] - 1
itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Seville'})
current_day = end_day + 1

# Fly to Milan
flight_day = 12
itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Seville', 'to': 'Milan'})

# Stay in Milan
start_day = flight_day
end_day = start_day + cities['Milan'] - 1
itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Milan'})
current_day = end_day + 1

# Fly to Stockholm
flight_day = 14
itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Milan', 'to': 'Stockholm'})

# Stay in Stockholm
start_day = flight_day
end_day = start_day + cities['Stockholm'] - 1
itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Stockholm'})
current_day = end_day + 1

# Fly to Tallinn
flight_day = 18
itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Stockholm', 'to': 'Tallinn'})

# Stay in Tallinn
start_day = flight_day
end_day = start_day + cities['Tallinn'] - 1
itinerary.append({'day_range': f'Day {start_day}-{end_day}', 'place': 'Tallinn'})
current_day = end_day + 1

# Output the itinerary
print(json.dumps(itinerary))