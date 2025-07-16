def correct_manual_solution():
    itinerary = [
        {'day_range': 'Day 1-7', 'place': 'Madrid'},
        {'day_range': 'Day 7', 'place': 'Madrid'},
        {'day_range': 'Day 7', 'place': 'Paris'},
        {'day_range': 'Day 7-12', 'place': 'Paris'},
        {'day_range': 'Day 12', 'place': 'Paris'},
        {'day_range': 'Day 12', 'place': 'Seville'},
        {'day_range': 'Day 12-14', 'place': 'Seville'},
        {'day_range': 'Day 14', 'place': 'Seville'},
        {'day_range': 'Day 14', 'place': 'Bucharest'},
        {'day_range': 'Day 14-15', 'place': 'Bucharest'}
    ]
    return {'itinerary': itinerary}

print(correct_manual_solution())