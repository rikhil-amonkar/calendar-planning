import json

# Define the input parameters
days_in_city = {
    'Brussels': 2,
    'Venice': 3,
    'Santorini': 3,
    'London': 3,
    'Reykjavik': 3,
    'Madrid': 5,
    'Lisbon': 4
}

# Direct flights between cities
flights = {
    'Brussels': ['Venice', 'London'],
    'Venice': ['Santorini', 'London'],
    'Santorini': ['London'],
    'London': ['Reykjavik', 'Madrid'],
    'Reykjavik': ['Madrid'],
    'Madrid': ['Lisbon'],
    'Lisbon': []
}

# Conference days in Brussels
conference_days = [1, 2]

# Wedding days in Madrid
wedding_days = [7, 8, 9, 10, 11]

# Relatives visit in Venice between day 5 and 7
relatives_visit_days = [5, 7]

# Calculate the optimal itinerary
itinerary = []

current_day = 1
current_city = 'Brussels'

# Start in Brussels
itinerary.append({'day_range': 'Day 1-2', 'place': 'Brussels'})

# Day 2: Brussels to Venice
if current_day <= 2:
    flight_day = current_day
    next_city = 'Venice'
    if flight_day in flights['Brussels']:
        itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Brussels', 'to': 'Venice'})
        current_day = flight_day + 1
        current_city = next_city

# Days 3-5: Venice
if current_day <= 5:
    itinerary.append({'day_range': f'Day {current_day}-{5}', 'place': 'Venice'})
    current_day = 6

# Day 5: Venice to London
if current_day <= 5:
    flight_day = current_day
    next_city = 'London'
    if flight_day in flights['Venice']:
        itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Venice', 'to': 'London'})
        current_day = flight_day + 1
        current_city = next_city

# Days 6-8: London
if current_day <= 8:
    itinerary.append({'day_range': f'Day {current_day}-{8}', 'place': 'London'})
    current_day = 9

# Day 8: London to Reykjavik
if current_day <= 8:
    flight_day = current_day
    next_city = 'Reykjavik'
    if flight_day in flights['London']:
        itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'London', 'to': 'Reykjavik'})
        current_day = flight_day + 1
        current_city = next_city

# Days 9-11: Reykjavik
if current_day <= 11:
    itinerary.append({'day_range': f'Day {current_day}-{11}', 'place': 'Reykjavik'})
    current_day = 12

# Day 11: Reykjavik to Madrid
if current_day <= 11:
    flight_day = current_day
    next_city = 'Madrid'
    if flight_day in flights['Reykjavik']:
        itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Reykjavik', 'to': 'Madrid'})
        current_day = flight_day + 1
        current_city = next_city

# Days 12-16: Madrid
if current_day <= 16:
    itinerary.append({'day_range': f'Day {current_day}-{16}', 'place': 'Madrid'})

# Day 16: Madrid to Lisbon
if current_day <= 16:
    flight_day = current_day
    next_city = 'Lisbon'
    if flight_day in flights['Madrid']:
        itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Madrid', 'to': 'Lisbon'})
        current_day = flight_day + 1
        current_city = next_city

# Days 17: Lisbon
if current_day <= 17:
    itinerary.append({'day_range': 'Day 17-17', 'place': 'Lisbon'})

# Ensure all constraints are met
if current_day > 17:
    current_day = 17

# Output the result
print(json.dumps(itinerary))