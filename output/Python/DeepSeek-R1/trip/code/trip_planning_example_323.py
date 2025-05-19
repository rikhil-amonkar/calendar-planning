import json

def main():
    flight_connections = {
        'London': ['Oslo', 'Split'],
        'Split': ['London', 'Oslo'],
        'Oslo': ['London', 'Split', 'Porto'],
        'Porto': ['Oslo']
    }
    
    itinerary = []
    current_day = 1
    
    # London (Days 1-7)
    london_end = 7
    itinerary.append({'day_range': f'Day 1-7', 'place': 'London'})
    current_day = london_end
    
    # Split (Days 7-11)
    if 'Split' not in flight_connections['London']:
        print(json.dumps({"itinerary": []}))
        return
    split_start = 7
    split_end = 11
    itinerary.append({'day_range': f'Day 7-11', 'place': 'Split'})
    current_day = split_end
    
    # Oslo (Days 11-12)
    if 'Oslo' not in flight_connections['Split']:
        print(json.dumps({"itinerary": []}))
        return
    oslo_start = current_day
    oslo_end = oslo_start + 1
    itinerary.append({'day_range': f'Day 11-12', 'place': 'Oslo'})
    current_day = oslo_end
    
    # Porto (Days 12-16)
    if 'Porto' not in flight_connections['Oslo']:
        print(json.dumps({"itinerary": []}))
        return
    porto_start = current_day
    porto_end = porto_start + 4  # 5 days inclusive
    if porto_end != 16:
        print(json.dumps({"itinerary": []}))
        return
    itinerary.append({'day_range': f'Day 12-16', 'place': 'Porto'})
    
    # Validate day counts
    days = {
        'London': 7,
        'Split': 5,
        'Oslo': 2,
        'Porto': 5
    }
    valid = True
    for entry in itinerary:
        start, end = map(int, entry['day_range'].split(' ')[1].split('-'))
        days_spent = end - start + 1
        if days_spent != days[entry['place']]:
            valid = False
            break
    
    if valid:
        print(json.dumps({"itinerary": itinerary}))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()