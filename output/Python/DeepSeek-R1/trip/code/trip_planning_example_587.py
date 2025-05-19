import json

def main():
    cities = {
        'Manchester': {'days': 3, 'constraints': {'start': 1, 'end': 3}},
        'Venice': {'days': 7, 'constraints': {'start': 3, 'end': 9}},
        'Istanbul': {'days': 7},
        'Krakow': {'days': 6},
        'Lyon': {'days': 2}
    }
    
    flight_graph = {
        'Manchester': ['Venice', 'Istanbul', 'Krakow'],
        'Venice': ['Manchester', 'Istanbul', 'Lyon'],
        'Istanbul': ['Manchester', 'Venice', 'Krakow', 'Lyon'],
        'Krakow': ['Manchester', 'Istanbul'],
        'Lyon': ['Venice', 'Istanbul']
    }
    
    itinerary_order = ['Manchester', 'Venice', 'Lyon', 'Istanbul', 'Krakow']
    
    # Validate flight connections
    for i in range(len(itinerary_order)-1):
        if itinerary_order[i+1] not in flight_graph[itinerary_order[i]]:
            print(json.dumps({"itinerary": []}))
            return
    
    # Calculate day ranges
    current_day = 1
    itinerary = []
    for city in itinerary_order:
        details = cities[city]
        days = details['days']
        
        # Apply constraints
        if 'constraints' in details:
            const = details['constraints']
            if 'start' in const:
                current_day = const['start']
            if 'end' in const:
                end_day = const['end']
                current_day = end_day - days + 1
        
        end_day = current_day + days - 1
        itinerary.append({
            "day_range": f"Day {current_day}-{end_day}",
            "place": city
        })
        current_day = end_day
    
    # Verify total days
    if current_day != 21:
        print(json.dumps({"itinerary": []}))
        return
    
    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()