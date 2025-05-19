import json

def plan_trip():
    required_days = {
        'Riga': 2,
        'Amsterdam': 2,
        'Mykonos': 5
    }
    flight_graph = {
        'Amsterdam': ['Mykonos', 'Riga'],
        'Riga': ['Amsterdam'],
        'Mykonos': ['Amsterdam']
    }
    total_days = 7
    cities = ['Riga', 'Amsterdam', 'Mykonos']
    itinerary = []
    
    # Validate flight connections
    valid = True
    for i in range(len(cities) - 1):
        if cities[i+1] not in flight_graph[cities[i]]:
            valid = False
            break
    if not valid:
        print(json.dumps({"itinerary": []}))
        return
    
    current_day = 1
    for idx, city in enumerate(cities):
        req = required_days[city]
        start = current_day
        end = start + req - 1
        
        if idx == len(cities) - 1:
            end = total_days
            if end - start + 1 < req:
                print(json.dumps({"itinerary": []}))
                return
        
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })
        current_day = end
    
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    plan_trip()