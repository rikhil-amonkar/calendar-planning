import json

def main():
    cities_order = [
        {'name': 'Venice', 'days': 5},
        {'name': 'Edinburgh', 'days': 4},
        {'name': 'Krakow', 'days': 4},
        {'name': 'Stuttgart', 'days': 3},
        {'name': 'Split', 'days': 2},
        {'name': 'Athens', 'days': 4},
        {'name': 'Mykonos', 'days': 4}
    ]
    
    flight_graph = {
        'Venice': {'Edinburgh', 'Stuttgart', 'Athens'},
        'Edinburgh': {'Krakow', 'Stuttgart', 'Athens', 'Venice'},
        'Krakow': {'Split', 'Edinburgh', 'Stuttgart', 'Venice'},
        'Stuttgart': {'Venice', 'Krakow', 'Edinburgh', 'Athens', 'Split'},
        'Split': {'Krakow', 'Athens', 'Stuttgart'},
        'Athens': {'Split', 'Stuttgart', 'Edinburgh', 'Mykonos', 'Venice'},
        'Mykonos': {'Athens'}
    }
    
    for i in range(len(cities_order) - 1):
        current = cities_order[i]['name']
        next_city = cities_order[i+1]['name']
        if next_city not in flight_graph.get(current, set()):
            raise ValueError(f"No direct flight from {current} to {next_city}")
    
    start_day = 1
    itinerary = []
    for city in cities_order:
        name = city['name']
        days = city['days']
        end_day = start_day + days - 1
        day_range = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": name})
        start_day = end_day
    
    stuttgart_entry = next(e for e in itinerary if e['place'] == 'Stuttgart')
    start, end = map(int, stuttgart_entry['day_range'].split(' ')[1].split('-'))
    if not (start <= 11 and end >= 13):
        raise ValueError("Stuttgart days do not cover workshop period")
    
    split_entry = next(e for e in itinerary if e['place'] == 'Split')
    start, end = map(int, split_entry['day_range'].split(' ')[1].split('-'))
    if not (start <= 14 and end >= 13):
        raise ValueError("Split days do not cover meeting period")
    
    krakow_entry = next(e for e in itinerary if e['place'] == 'Krakow')
    start, end = map(int, krakow_entry['day_range'].split(' ')[1].split('-'))
    if not (start <= 11 and end >= 8):
        raise ValueError("Krakow days do not cover meeting period")
    
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()