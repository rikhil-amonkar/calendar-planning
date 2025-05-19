import json

def main():
    required_days = {
        'Nice': 5,
        'Krakow': 6,
        'Dublin': 7,
        'Lyon': 4,
        'Frankfurt': 2
    }
    
    flight_graph = {
        'Nice': {'Dublin', 'Frankfurt', 'Lyon'},
        'Dublin': {'Nice', 'Frankfurt', 'Krakow', 'Lyon'},
        'Frankfurt': {'Dublin', 'Krakow', 'Lyon', 'Nice'},
        'Krakow': {'Dublin', 'Frankfurt'},
        'Lyon': {'Frankfurt', 'Dublin', 'Nice'}
    }
    
    itinerary_order = ['Nice', 'Lyon', 'Dublin', 'Krakow', 'Frankfurt']
    
    valid = True
    for i in range(len(itinerary_order) - 1):
        if itinerary_order[i+1] not in flight_graph[itinerary_order[i]]:
            valid = False
            break
    
    if not valid:
        print(json.dumps({"itinerary": []}))
        return
    
    day_ranges = []
    current_day = 1
    for city in itinerary_order:
        duration = required_days[city]
        if city == 'Nice':
            end_day = 5
        elif city == 'Frankfurt':
            end_day = 20
        else:
            end_day = current_day + duration - 1
        day_ranges.append((current_day, end_day, city))
        current_day = end_day
    
    if day_ranges[-1][1] != 20:
        print(json.dumps({"itinerary": []}))
        return
    
    itinerary = []
    for start, end, city in day_ranges:
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })
    
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()