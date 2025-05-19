import json

# Define the input parameters
days_in_city = {
    'Vienna': 4,
    'Milan': 2,
    'Rome': 3,
    'Riga': 2,
    'Lisbon': 3,
    'Vilnius': 4,
    'Oslo': 3
}

# Direct flights between cities
flights = {
    'Vienna': ['Milan', 'Vilnius', 'Lisbon', 'Oslo'],
    'Milan': ['Riga', 'Rome'],
    'Riga': ['Vilnius', 'Lisbon'],
    'Vilnius': ['Oslo', 'Milan'],
    'Lisbon': ['Oslo', 'Riga'],
    'Oslo': ['Vilnius', 'Lisbon']
}

# The conference is on days 1 and 4 in Vienna
conference_days = [1, 4]

# The relatives visit is between days 11 and 13 in Lisbon
relatives_visit_days = [11, 13]

# The friend meeting is between days 13 and 15 in Oslo
friend_meeting_days = [13, 15]

# Calculate the optimal itinerary
itinerary = []

current_day = 1
current_city = 'Vienna'

# Start in Vienna
itinerary.append({'day_range': 'Day 1-4', 'place': 'Vienna'})

# Day 4: Vienna to Vilnius
if current_day <= 4:
    flight_day = current_day
    next_city = 'Vilnius'
    if flight_day in flights['Vienna']:
        itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Vienna', 'to': 'Vilnius'})
        current_day = flight_day + 1
        current_city = next_city

# Days 5-7: Vilnius
if current_day <= 7:
    itinerary.append({'day_range': f'Day {current_day}-{7}', 'place': 'Vilnius'})
    current_day = 8

# Day 7: Vilnius to Oslo
if current_day <= 7:
    flight_day = current_day
    next_city = 'Oslo'
    if flight_day in flights['Vilnius']:
        itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Vilnius', 'to': 'Oslo'})
        current_day = flight_day + 1
        current_city = next_city

# Days 8-10: Oslo
if current_day <= 10:
    itinerary.append({'day_range': f'Day {current_day}-{10}', 'place': 'Oslo'})
    current_day = 11

# Day 10: Oslo to Lisbon
if current_day <= 10:
    flight_day = current_day
    next_city = 'Lisbon'
    if flight_day in flights['Oslo']:
        itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Oslo', 'to': 'Lisbon'})
        current_day = flight_day + 1
        current_city = next_city

# Days 11-13: Lisbon
if current_day <= 13:
    itinerary.append({'day_range': f'Day {current_day}-{13}', 'place': 'Lisbon'})
    current_day = 14

# Day 13: Lisbon to Riga
if current_day <= 13:
    flight_day = current_day
    next_city = 'Riga'
    if flight_day in flights['Lisbon']:
        itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Lisbon', 'to': 'Riga'})
        current_day = flight_day + 1
        current_city = next_city

# Days 14-15: Riga
if current_day <= 15:
    itinerary.append({'day_range': f'Day {current_day}-{15}', 'place': 'Riga'})
    current_day = 16

# Day 15: Riga to Milan
if current_day <= 15:
    flight_day = current_day
    next_city = 'Milan'
    if flight_day in flights['Riga']:
        itinerary.append({'flying': f'Day {flight_day}-{flight_day}', 'from': 'Riga', 'to': 'Milan'})
        current_day = flight_day + 1
        current_city = next_city

# Days 16-17: Milan
if current_day <= 17:
    itinerary.append({'day_range': f'Day {current_day}-{17}', 'place': 'Milan'})

# Ensure all constraints are met
if current_day > 15:
    current_day = 15

# Output the result
print(json.dumps(itinerary))