import json

def main():
    flight_graph = {
        'Mykonos': {'London', 'Nice'},
        'London': {'Mykonos', 'Copenhagen', 'Oslo', 'Nice'},
        'Copenhagen': {'London', 'Tallinn', 'Oslo', 'Nice'},
        'Tallinn': {'Copenhagen', 'Oslo'},
        'Oslo': {'Tallinn', 'London', 'Copenhagen', 'Nice'},
        'Nice': {'Mykonos', 'London', 'Oslo', 'Copenhagen'}
    }

    itinerary_order = [
        ('Mykonos', 4),
        ('London', 2),
        ('Copenhagen', 3),
        ('Tallinn', 4),
        ('Oslo', 5),
        ('Nice', 3)
    ]

    current_day = 1
    itinerary = []
    prev_city = None

    for city, days in itinerary_order:
        if prev_city is not None:
            if city not in flight_graph[prev_city]:
                raise ValueError(f"No direct flight from {prev_city} to {city}")
        start = current_day
        end = current_day + days - 1
        itinerary.append({
            'day_range': f"Day {start}-{end}",
            'place': city
        })
        current_day = end

    required_days = {
        'Mykonos': 4, 'London': 2, 'Copenhagen': 3,
        'Tallinn': 4, 'Oslo': 5, 'Nice': 3
    }

    for entry in itinerary:
        city = entry['place']
        start, end = map(int, entry['day_range'].split()[1].split('-'))
        if end - start + 1 != required_days[city]:
            raise ValueError(f"Duration mismatch for {city}")

    oslo_entry = next(e for e in itinerary if e['place'] == 'Oslo')
    oslo_start = int(oslo_entry['day_range'].split()[1].split('-')[0])
    oslo_end = int(oslo_entry['day_range'].split('-')[1])
    if not (10 <= oslo_start <= 14 and 10 <= oslo_end <= 14):
        raise ValueError("Oslo visit doesn't meet friend constraint")

    nice_entry = next(e for e in itinerary if e['place'] == 'Nice')
    nice_start = int(nice_entry['day_range'].split()[1].split('-')[0])
    nice_end = int(nice_entry['day_range'].split('-')[1])
    if nice_start != 14 or nice_end != 16:
        raise ValueError("Nice visit doesn't meet conference days")

    print(json.dumps({'itinerary': itinerary})

if __name__ == "__main__":
    main()