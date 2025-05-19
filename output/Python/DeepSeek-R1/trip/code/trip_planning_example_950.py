import json

def main():
    cities = {
        'Rome': {'required_days': 4, 'fixed_start': 1, 'fixed_end': 4},
        'Mykonos': {'required_days': 3, 'fixed_start': 4, 'fixed_end': 6},
        'Krakow': {'required_days': 2, 'fixed_start': 16, 'fixed_end': 17},
        'Riga': {'required_days': 3},
        'Munich': {'required_days': 4},
        'Bucharest': {'required_days': 4},
        'Nice': {'required_days': 3}
    }

    flight_routes = {
        'Rome': ['Nice', 'Munich', 'Mykonos', 'Bucharest', 'Riga'],
        'Nice': ['Rome', 'Riga', 'Mykonos', 'Munich'],
        'Riga': ['Nice', 'Bucharest', 'Munich'],
        'Bucharest': ['Munich', 'Riga', 'Rome'],
        'Munich': ['Bucharest', 'Mykonos', 'Rome', 'Nice', 'Krakow'],
        'Mykonos': ['Munich', 'Nice', 'Rome'],
        'Krakow': ['Munich'],
        'Mykonos': ['Munich', 'Nice', 'Rome']
    }

    itinerary = [
        {'place': 'Rome', 'start': 1, 'end': 4},
        {'place': 'Mykonos', 'start': 4, 'end': 6}
    ]

    middle_cities = ['Nice', 'Riga', 'Bucharest', 'Munich']
    current_city = 'Mykonos'
    current_day = 6

    for next_city in middle_cities:
        if next_city == current_city:
            continue
        if next_city not in flight_routes.get(current_city, []):
            continue
        required_days = cities[next_city]['required_days']
        start_day = current_day
        end_day = start_day + required_days - 1
        if next_city == 'Munich':
            end_day = 16
        if end_day > 16:
            continue
        itinerary.append({'place': next_city, 'start': start_day, 'end': end_day})
        current_day = end_day
        current_city = next_city

    itinerary.append({'place': 'Krakow', 'start': 16, 'end': 17})

    itinerary = sorted(itinerary, key=lambda x: x['start'])
    result = {'itinerary': []}
    for segment in itinerary:
        start = segment['start']
        end = segment['end']
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        result['itinerary'].append({'day_range': day_range, 'place': segment['place']})

    print(json.dumps(result))

if __name__ == "__main__":
    main()