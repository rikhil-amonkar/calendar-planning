import json

def main():
    cities = [
        {'name': 'Berlin', 'duration': 5, 'fixed': (1, 5)},
        {'name': 'Split', 'duration': 3},
        {'name': 'Lyon', 'duration': 5, 'fixed': (7, 11)},
        {'name': 'Bucharest', 'duration': 3, 'fixed': (13, 15)},
        {'name': 'Riga', 'duration': 5},
        {'name': 'Lisbon', 'duration': 3},
        {'name': 'Tallinn', 'duration': 4}
    ]
    
    flights = {
        'Berlin': {'Split', 'Lisbon', 'Riga', 'Tallinn'},
        'Split': {'Berlin', 'Lyon'},
        'Lyon': {'Split', 'Lisbon', 'Bucharest'},
        'Bucharest': {'Lisbon', 'Riga', 'Lyon'},
        'Riga': {'Berlin', 'Bucharest', 'Split', 'Lisbon', 'Tallinn'},
        'Lisbon': {'Berlin', 'Riga', 'Lyon', 'Bucharest'},
        'Tallinn': {'Riga', 'Berlin'}
    }
    
    itinerary = [
        {'day_range': 'Day 1-5', 'place': 'Berlin'},
        {'day_range': 'Day 5-7', 'place': 'Split'},
        {'day_range': 'Day 7-11', 'place': 'Lyon'},
        {'day_range': 'Day 11-13', 'place': 'Lisbon'},
        {'day_range': 'Day 13-15', 'place': 'Bucharest'},
        {'day_range': 'Day 15-19', 'place': 'Riga'},
        {'day_range': 'Day 19-22', 'place': 'Tallinn'}
    ]
    
    # Verify transitions
    prev_city = None
    for segment in itinerary:
        current_city = segment['place']
        if prev_city is not None:
            assert current_city in flights[prev_city], f"No flight from {prev_city} to {current_city}"
        prev_city = current_city
    
    # Verify durations
    total_days = 0
    for seg in itinerary:
        days = seg['day_range']
        start, end = map(int, days.split('-')[0].split()[1:])
        duration = end - start + 1
        city = next(c for c in cities if c['name'] == seg['place'])
        if 'fixed' in city:
            assert duration == city['duration'], f"Duration mismatch for {city['name']}"
        else:
            assert duration == city['duration'], f"Duration mismatch for {city['name']}"
    
    print(json.dumps({'itinerary': itinerary}, indent=2))

if __name__ == "__main__":
    main()