import json
from itertools import permutations

def main():
    cities = [
        {'name': 'Valencia', 'days': 4},
        {'name': 'Naples', 'days': 4},
        {'name': 'Manchester', 'days': 4},
        {'name': 'Oslo', 'days': 3}
    ]
    
    flight_connections = {
        'Valencia': ['Frankfurt', 'Naples'],
        'Naples': ['Manchester', 'Frankfurt', 'Oslo', 'Valencia'],
        'Manchester': ['Frankfurt', 'Naples', 'Oslo'],
        'Oslo': ['Frankfurt', 'Vilnius', 'Manchester', 'Naples'],
        'Vilnius': ['Frankfurt', 'Oslo'],
        'Frankfurt': ['Valencia', 'Manchester', 'Naples', 'Oslo', 'Vilnius']
    }

    valid_perm = None
    for perm in permutations(cities):
        if perm[-1]['name'] != 'Oslo':
            continue
        valid = True
        for i in range(len(perm)-1):
            if perm[i+1]['name'] not in flight_connections[perm[i]['name']]:
                valid = False
                break
        if valid:
            valid_perm = perm
            break

    if not valid_perm:
        raise ValueError("No valid itinerary found")

    itinerary = []
    current_day = 1
    for city in valid_perm:
        end_day = current_day + city['days'] - 1
        itinerary.append({
            'day_range': f"Day {current_day}-{end_day}",
            'place': city['name']
        })
        current_day = end_day

    itinerary.append({
        'day_range': f"Day {current_day}-{current_day + 1}",
        'place': 'Vilnius'
    })
    current_day += 1

    itinerary.append({
        'day_range': f"Day {current_day}-{current_day + 3}",
        'place': 'Frankfurt'
    })

    print(json.dumps({'itinerary': itinerary}, indent=2))

if __name__ == "__main__":
    main()