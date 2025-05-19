import json

def main():
    cities = {
        'Salzburg': {'duration': 2, 'fixed': None},
        'Venice': {'duration': 5, 'fixed': None},
        'Bucharest': {'duration': 4, 'fixed': None},
        'Brussels': {'duration': 2, 'fixed': (21, 22)},
        'Hamburg': {'duration': 4, 'fixed': None},
        'Copenhagen': {'duration': 4, 'fixed': (18, 21)},
        'Nice': {'duration': 3, 'fixed': (9, 11)},
        'Zurich': {'duration': 5, 'fixed': None},
        'Naples': {'duration': 4, 'fixed': (22, 25)}
    }
    
    flight_graph = {
        'Salzburg': ['Hamburg'],
        'Hamburg': ['Salzburg', 'Venice', 'Bucharest', 'Brussels', 'Copenhagen', 'Nice', 'Zurich'],
        'Venice': ['Hamburg', 'Brussels', 'Naples', 'Copenhagen', 'Zurich', 'Nice'],
        'Nice': ['Zurich', 'Hamburg', 'Brussels', 'Venice', 'Copenhagen', 'Naples'],
        'Zurich': ['Brussels', 'Naples', 'Hamburg', 'Copenhagen', 'Bucharest', 'Nice', 'Venice'],
        'Bucharest': ['Copenhagen', 'Hamburg', 'Brussels', 'Naples', 'Zurich'],
        'Copenhagen': ['Bucharest', 'Venice', 'Hamburg', 'Zurich', 'Brussels', 'Naples'],
        'Brussels': ['Zurich', 'Venice', 'Bucharest', 'Hamburg', 'Copenhagen', 'Nice', 'Naples'],
        'Naples': ['Zurich', 'Venice', 'Bucharest', 'Copenhagen', 'Brussels', 'Nice']
    }
    
    itinerary_order = [
        ('Salzburg', 2),
        ('Hamburg', 4),
        ('Venice', 5),
        ('Nice', 3),
        ('Zurich', 5),
        ('Bucharest', 4),
        ('Copenhagen', 4),
        ('Brussels', 2),
        ('Naples', 4)
    ]
    
    current_day = 1
    itinerary = []
    
    for city, duration in itinerary_order:
        end_day = current_day + duration - 1
        fixed = cities[city]['fixed']
        if fixed:
            start_fixed, end_fixed = fixed
            if (current_day <= start_fixed and end_day >= end_fixed):
                current_day = end_fixed + 1
                itinerary.append({'day_range': f"Day {start_fixed}-{end_fixed}", 'place': city})
            else:
                start_day = fixed[0]
                end_day = fixed[1]
                itinerary.append({'day_range': f"Day {start_day}-{end_day}", 'place': city})
                current_day = end_day + 1
        else:
            if itinerary:
                prev_city = itinerary[-1]['place']
                if city not in flight_graph.get(prev_city, []):
                    raise ValueError(f"No flight from {prev_city} to {city}")
            itinerary.append({'day_range': f"Day {current_day}-{end_day}", 'place': city})
            current_day = end_day + 1
    
    output = {'itinerary': itinerary}
    print(json.dumps(output))

if __name__ == "__main__":
    main()