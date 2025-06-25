import json

def build_flight_graph():
    flights = [
        ('Split', 'Munich'),
        ('Munich', 'Manchester'),
        ('Hamburg', 'Manchester'),
        ('Hamburg', 'Munich'),
        ('Split', 'Lyon'),
        ('Lyon', 'Munich'),
        ('Hamburg', 'Split'),
        ('Manchester', 'Split')
    ]
    graph = {}
    for city1, city2 in flights:
        if city1 not in graph:
            graph[city1] = set()
        if city2 not in graph:
            graph[city2] = set()
        graph[city1].add(city2)
        graph[city2].add(city1)
    return graph

def main():
    graph = build_flight_graph()
    
    segments = [
        {'start': 1, 'end': 7, 'city': None},
        {'start': 7, 'end': 13, 'city': None},
        {'start': 13, 'end': 14, 'city': 'Lyon'},
        {'start': 14, 'end': 19, 'city': 'Munich'},
        {'start': 19, 'end': 20, 'city': 'Manchester'}
    ]
    
    candidates = ['Hamburg', 'Split']
    permutations = [(candidates[0], candidates[1]), (candidates[1], candidates[0])]
    
    valid_itinerary = None
    for perm in permutations:
        segments[0]['city'] = perm[0]
        segments[1]['city'] = perm[1]
        
        valid = True
        for i in range(len(segments) - 1):
            city1 = segments[i]['city']
            city2 = segments[i+1]['city']
            if city2 not in graph.get(city1, set()):
                valid = False
                break
        if valid:
            valid_itinerary = [dict(seg) for seg in segments]
            break
    
    if valid_itinerary is None:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    itinerary_output = []
    for seg in valid_itinerary:
        day_range = f"Day {seg['start']}-{seg['end']}"
        place = seg['city']
        itinerary_output.append({"day_range": day_range, "place": place})
    
    result = {"itinerary": itinerary_output}
    print(json.dumps(result))

if __name__ == "__main__":
    main()