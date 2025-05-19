import json

# Define trip parameters
trip_plan = {
    'cities': {
        'Berlin': {'days': 5, 'start_day': 1, 'event': 'annual show'},
        'Split': {'days': 3, 'start_day': None},
        'Bucharest': {'days': 3, 'start_day': 13},
        'Riga': {'days': 5, 'start_day': None},
        'Lisbon': {'days': 3, 'start_day': None},
        'Tallinn': {'days': 4, 'start_day': None},
        'Lyon': {'days': 5, 'start_day': 7, 'event': 'wedding'}
    },
    'direct_flights': [
        ('Lisbon', 'Bucharest'), ('Berlin', 'Lisbon'), ('Bucharest', 'Riga'),
        ('Berlin', 'Riga'), ('Split', 'Lyon'), ('Lisbon', 'Riga'),
        ('Riga', 'Tallinn'), ('Berlin', 'Split'), ('Lyon', 'Lisbon'),
        ('Berlin', 'Tallinn'), ('Lyon', 'Bucharest')
    ],
    'total_days': 22
}

# Create initial itinerary based on the constraints
itinerary = []
current_day = 1

# Add Berlin stay
itinerary.append({'day_range': 'Day 1-5', 'place': 'Berlin'})
current_day += 5

# Add wedding in Lyon
itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Berlin', 'to': 'Lyon'})
current_day += 1
itinerary.append({'day_range': 'Day 7-11', 'place': 'Lyon'})
current_day += 5

# Add Split after Lyon
itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Lyon', 'to': 'Split'})
current_day += 1
itinerary.append({'day_range': 'Day {current_day}-{current_day + 2}', 'place': 'Split'})
current_day += 3

# Add Bucharest
itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Split', 'to': 'Bucharest'})
current_day += 1
itinerary.append({'day_range': 'Day 13-15', 'place': 'Bucharest'})
current_day += 3

# Add Riga
itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Bucharest', 'to': 'Riga'})
current_day += 1
itinerary.append({'day_range': 'Day {current_day}-{current_day + 4}', 'place': 'Riga'})
current_day += 5

# Add Tallinn
itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Riga', 'to': 'Tallinn'})
current_day += 1
itinerary.append({'day_range': 'Day {current_day}-{current_day + 3}', 'place': 'Tallinn'})
current_day += 4

# Add Lisbon
itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Tallinn', 'to': 'Lisbon'})
current_day += 1
itinerary.append({'day_range': 'Day {current_day}-{current_day + 2}', 'place': 'Lisbon'})
current_day += 3

# Output result as JSON
output_json = json.dumps(itinerary, indent=4)
print(output_json)