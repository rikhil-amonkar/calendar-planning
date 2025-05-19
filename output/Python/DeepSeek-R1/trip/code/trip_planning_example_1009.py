import json

def main():
    cities = {
        'Reykjavik': 4,
        'Stuttgart': 5,
        'Manchester': 5,
        'Istanbul': 2,
        'Riga': 4,
        'Bucharest': 4,
        'Vienna': 2,
        'Florence': 4
    }
    
    flight_graph = {
        'Reykjavik': ['Stuttgart', 'Vienna'],
        'Stuttgart': ['Reykjavik', 'Vienna', 'Istanbul', 'Manchester'],
        'Manchester': ['Stuttgart', 'Vienna', 'Riga', 'Istanbul', 'Bucharest'],
        'Istanbul': ['Stuttgart', 'Manchester', 'Riga', 'Bucharest', 'Vienna'],
        'Riga': ['Manchester', 'Vienna', 'Bucharest', 'Istanbul'],
        'Bucharest': ['Riga', 'Istanbul', 'Vienna', 'Manchester'],
        'Vienna': ['Bucharest', 'Reykjavik', 'Manchester', 'Riga', 'Istanbul', 'Florence', 'Stuttgart'],
        'Florence': ['Vienna']
    }
    
    fixed_events = {
        'Istanbul': (12, 13),
        'Bucharest': (16, 19)
    }
    
    order = [
        'Reykjavik',
        'Stuttgart',
        'Manchester',
        'Istanbul',
        'Riga',
        'Bucharest',
        'Vienna',
        'Florence'
    ]
    
    valid = True
    for i in range(len(order) - 1):
        if order[i+1] not in flight_graph.get(order[i], []):
            valid = False
            break
    
    if not valid:
        print(json.dumps({"itinerary": []}))
        return
    
    itinerary = []
    prev_departure = 0
    for city in order:
        arrival = prev_departure + 1 if prev_departure != 0 else 1
        if city in fixed_events:
            req_start, req_end = fixed_events[city]
            if arrival != req_start:
                valid = False
                break
            departure = req_end
        else:
            duration = cities[city]
            departure = arrival + duration - 1
        itinerary.append((arrival, departure, city))
        prev_departure = departure
    
    if prev_departure != 23:
        valid = False
    
    if not valid:
        print(json.dumps({"itinerary": []}))
        return
    
    json_output = {"itinerary": []}
    for entry in itinerary:
        start, end, place = entry
        day_range = f"Day {start}-{end}" if start != end else f"Day {start}"
        json_output["itinerary"].append({"day_range": day_range, "place": place})
    
    print(json.dumps(json_output, indent=2))

if __name__ == "__main__":
    main()