def generate_itinerary():
    itinerary = [
        {'day_range': 'Day 1-4', 'place': 'Madrid'},
        {'day_range': 'Day 5-7', 'place': 'Porto'},
        {'day_range': 'Day 8-9', 'place': 'Seville'},
        {'day_range': 'Day 10-13', 'place': 'Stuttgart'}
    ]
    return {'itinerary': itinerary}

print(generate_itinerary())