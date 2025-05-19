import json

def main():
    cities = [
        {'name': 'Edinburgh', 'days': 5, 'fixed': (1, 5)},
        {'name': 'Barcelona', 'days': 5},
        {'name': 'Budapest', 'days': 5, 'fixed': (9, 13)},
        {'name': 'Vienna', 'days': 5},
        {'name': 'Stockholm', 'days': 2, 'fixed': (17, 18)},
        {'name': 'Munich', 'days': 3, 'fixed': (18, 20)},
        {'name': 'Bucharest', 'days': 2},
        {'name': 'Riga', 'days': 5},
        {'name': 'Warsaw', 'days': 5, 'fixed': (25, 29)},
        {'name': 'Krakow', 'days': 4}
    ]
    
    direct_flights = {
        ('Edinburgh', 'Barcelona'), ('Barcelona', 'Budapest'),
        ('Budapest', 'Vienna'), ('Vienna', 'Stockholm'),
        ('Stockholm', 'Munich'), ('Munich', 'Bucharest'),
        ('Bucharest', 'Riga'), ('Riga', 'Warsaw'), ('Warsaw', 'Krakow')
    }
    
    itinerary = []
    current_day = 1
    
    for i in range(len(cities)):
        city = cities[i]
        name = city['name']
        days = city['days']
        
        if 'fixed' in city:
            start, end = city['fixed']
            itinerary.append({'day_range': f'Day {start}-{end}', 'place': name})
            current_day = end + 1
        else:
            if i > 0:
                prev_city = cities[i-1]['name']
                if (prev_city, name) not in direct_flights and (name, prev_city) not in direct_flights:
                    raise ValueError(f'No direct flight from {prev_city} to {name}')
            
            end = current_day + days - 1
            if end > 32:
                raise ValueError('Exceeded 32 days')
            itinerary.append({'day_range': f'Day {current_day}-{end}', 'place': name})
            current_day = end + 1
    
    print(json.dumps({'itinerary': itinerary}))

if __name__ == '__main__':
    main()