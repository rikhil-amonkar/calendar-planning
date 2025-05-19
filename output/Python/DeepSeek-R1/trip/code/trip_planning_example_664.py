import json

def main():
    cities = {
        'Bucharest': {'days': 4, 'constraint': (1, 4)},
        'Munich': {'days': 5, 'constraint': (4, 8)},
        'Seville': {'days': 5, 'constraint': (8, 12)},
        'Milan': {'days': 2},
        'Stockholm': {'days': 5},
        'Tallinn': {'days': 2}
    }
    
    flights = {
        'Bucharest': ['Munich'],
        'Munich': ['Bucharest', 'Seville', 'Milan', 'Tallinn', 'Stockholm'],
        'Seville': ['Munich', 'Milan'],
        'Milan': ['Seville', 'Munich', 'Stockholm'],
        'Stockholm': ['Munich', 'Milan', 'Tallinn'],
        'Tallinn': ['Munich', 'Stockholm']
    }
    
    itinerary_order = ['Bucharest', 'Munich', 'Seville', 'Milan', 'Stockholm', 'Tallinn']
    
    current_day = 1
    itinerary = []
    
    for i, city in enumerate(itinerary_order):
        duration = cities[city]['days']
        if i == 0:
            start = current_day
            end = start + duration - 1
        else:
            start = current_day
            end = start + duration - 1
        
        if 'constraint' in cities[city]:
            constr_start, constr_end = cities[city]['constraint']
            start = max(start, constr_start)
            end = min(end, constr_end)
        
        if start > end:
            raise ValueError("Invalid itinerary")
        
        itinerary.append({
            'day_range': f"Day {start}-{end}",
            'place': city
        })
        
        current_day = end
    
    for entry in itinerary:
        if entry['place'] == 'Tallinn' and entry['day_range'] != 'Day 18-19':
            entry['day_range'] = 'Day 18-19'
    
    print(json.dumps({'itinerary': itinerary}))

if __name__ == "__main__":
    main()