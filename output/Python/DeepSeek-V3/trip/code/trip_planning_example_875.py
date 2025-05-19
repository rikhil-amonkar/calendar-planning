import json
from itertools import permutations

def find_valid_itinerary():
    # Parameters
    total_days = 20
    cities = {
        'Stuttgart': {'duration': 3, 'constraints': [{'start': 11, 'end': 13}]},
        'Edinburgh': {'duration': 4, 'constraints': []},
        'Athens': {'duration': 4, 'constraints': []},
        'Split': {'duration': 2, 'constraints': [{'start': 13, 'end': 14}]},
        'Krakow': {'duration': 4, 'constraints': [{'start': 8, 'end': 11}]},
        'Venice': {'duration': 5, 'constraints': []},
        'Mykonos': {'duration': 4, 'constraints': []}
    }
    
    direct_flights = {
        'Krakow': ['Split', 'Stuttgart', 'Edinburgh'],
        'Split': ['Krakow', 'Athens', 'Stuttgart'],
        'Edinburgh': ['Krakow', 'Stuttgart', 'Venice', 'Athens'],
        'Venice': ['Stuttgart', 'Edinburgh', 'Athens'],
        'Stuttgart': ['Venice', 'Krakow', 'Edinburgh', 'Athens', 'Split'],
        'Athens': ['Split', 'Stuttgart', 'Edinburgh', 'Venice', 'Mykonos'],
        'Mykonos': ['Athens']
    }
    
    # Generate all possible permutations of the cities
    city_names = list(cities.keys())
    for perm in permutations(city_names):
        itinerary = list(perm)
        # Check if all flights are direct
        valid = True
        for i in range(len(itinerary)-1):
            if itinerary[i+1] not in direct_flights[itinerary[i]]:
                valid = False
                break
        if not valid:
            continue
        
        # Assign days and check constraints
        day = 1
        schedule = []
        prev_city = None
        for city in itinerary:
            duration = cities[city]['duration']
            if prev_city is not None:
                schedule.append({
                    'flying': f'Day {day}-{day}',
                    'from': prev_city,
                    'to': city
                })
            schedule.append({
                'day_range': f'Day {day}-{day + duration - 1}',
                'place': city
            })
            # Check constraints
            for constraint in cities[city]['constraints']:
                start = constraint['start']
                end = constraint['end']
                if not (day <= start and day + duration - 1 >= end):
                    valid = False
                    break
            if not valid:
                break
            day += duration
            prev_city = city
        
        if valid and day - 1 == total_days:
            return schedule
    
    return None

def main():
    itinerary = find_valid_itinerary()
    if itinerary:
        print(json.dumps(itinerary, indent=2))
    else:
        print(json.dumps({"error": "No valid itinerary found"}, indent=2))

if __name__ == "__main__":
    main()