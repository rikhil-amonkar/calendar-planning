def generate_itinerary():
    itinerary = []
    # Madrid: Days 1-4
    for day in range(1, 5):
        itinerary.append({'day_range': f'Day {day}', 'place': 'Madrid'})
    
    # Porto: Days 5-7
    for day in range(5, 8):
        itinerary.append({'day_range': f'Day {day}', 'place': 'Porto'})
    
    # Seville: Days 8-9
    for day in range(8, 10):
        itinerary.append({'day_range': f'Day {day}', 'place': 'Seville'})
    
    # Stuttgart: Days 10-13
    for day in range(10, 14):
        itinerary.append({'day_range': f'Day {day}', 'place': 'Stuttgart'})
    
    return {'itinerary': itinerary}

# Test the function
print(generate_itinerary())