import json

def main():
    cities = [
        {'name': 'Brussels', 'days': 3},
        {'name': 'Milan', 'days': 4},
        {'name': 'Split', 'days': 4},
        {'name': 'Helsinki', 'days': 3},
        {'name': 'Dubrovnik', 'days': 2}
    ]
    fixed = [
        {'name': 'Istanbul', 'start': 1, 'end': 5},
        {'name': 'Frankfurt', 'start': 16, 'end': 18},
        {'name': 'Vilnius', 'start': 18, 'end': 22}
    ]
    flights = {
        'Brussels': ['Vilnius', 'Helsinki', 'Istanbul', 'Milan', 'Frankfurt'],
        'Milan': ['Frankfurt', 'Split', 'Vilnius', 'Brussels', 'Helsinki', 'Istanbul'],
        'Split': ['Frankfurt', 'Milan', 'Vilnius', 'Helsinki'],
        'Helsinki': ['Brussels', 'Vilnius', 'Dubrovnik', 'Frankfurt', 'Split', 'Milan', 'Istanbul'],
        'Dubrovnik': ['Istanbul', 'Frankfurt'],
        'Frankfurt': ['Milan', 'Split', 'Helsinki', 'Dubrovnik', 'Vilnius'],
        'Istanbul': ['Brussels', 'Helsinki', 'Milan', 'Vilnius', 'Frankfurt'],
        'Vilnius': ['Brussels', 'Milan', 'Helsinki', 'Split', 'Frankfurt', 'Istanbul']
    }
    order = ['Brussels', 'Milan', 'Split', 'Helsinki', 'Dubrovnik']
    valid = True
    prev = 'Istanbul'
    for city in order:
        if city not in flights[prev]:
            valid = False
            break
        prev = city
    if 'Frankfurt' not in flights['Dubrovnik']:
        valid = False
    if not valid:
        print(json.dumps({'itinerary': []}))
        return
    
    itinerary = [{'day_range': 'Day 1-5', 'place': 'Istanbul'}]
    current_day = 5
    for city in order:
        days = next(c['days'] for c in cities if c['name'] == city)
        end = current_day + days - 1
        itinerary.append({'day_range': f'Day {current_day}-{end}', 'place': city})
        current_day = end
    itinerary.append({'day_range': 'Day 16-18', 'place': 'Frankfurt'})
    itinerary.append({'day_range': 'Day 18-22', 'place': 'Vilnius'})
    print(json.dumps({'itinerary': itinerary}))

if __name__ == '__main__':
    main()