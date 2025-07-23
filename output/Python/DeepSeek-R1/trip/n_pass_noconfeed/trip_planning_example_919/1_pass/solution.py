import json

def main():
    non_travel_days = {
        'Rome': 1,
        'Riga': 0,
        'Vilnius': 2,
        'Milan': 0,
        'Lisbon': 1,
        'Oslo': 2
    }
    next_cities = ['Rome', 'Riga', 'Vilnius', 'Milan', 'Lisbon', 'Oslo']
    
    itinerary = [
        {'day_range': 'Day 1-4', 'place': 'Vienna'}
    ]
    
    current_start = 4
    for i, city in enumerate(next_cities):
        if i < len(next_cities) - 1:
            end_day = current_start + non_travel_days[city] + 1
        else:
            end_day = current_start + non_travel_days[city]
        
        itinerary.append({
            'day_range': f"Day {current_start}-{end_day}",
            'place': city
        })
        
        current_start = end_day
    
    result = {'itinerary': itinerary}
    print(json.dumps(result))

if __name__ == '__main__':
    main()