def correct_manual_solution():
    itinerary = [
        {'day_range': 'Day 1-7', 'place': 'Madrid'},
        {'day_range': 'Day 7', 'place': 'Madrid'},
        {'day_range': 'Day 7', 'place': 'Paris'},
        {'day_range': 'Day 7-8', 'place': 'Paris'},
        {'day_range': 'Day 8', 'place': 'Paris'},
        {'day_range': 'Day 8', 'place': 'Bucharest'},
        {'day_range': 'Day 8-15', 'place': 'Bucharest'}
    ]
    return {'itinerary': itinerary}

print(correct_manual_solution())