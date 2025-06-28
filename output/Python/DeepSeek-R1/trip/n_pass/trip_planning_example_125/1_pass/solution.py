import json

def main():
    total_days = 15
    cities_info = {
        'Stuttgart': {'required_days': 6, 'constraint': (1, 6)},
        'Seville': {'required_days': 7},
        'Manchester': {'required_days': 4}
    }
    flights = [('Manchester', 'Seville'), ('Stuttgart', 'Manchester')]
    
    graph = {}
    for u, v in flights:
        if u not in graph:
            graph[u] = []
        if v not in graph:
            graph[v] = []
        graph[u].append(v)
        graph[v].append(u)
    
    endpoints = [city for city in graph if len(graph[city]) == 1]
    hub_candidates = [city for city in graph if len(graph[city]) == 2]
    if hub_candidates:
        hub = hub_candidates[0]
    else:
        hub = None
    
    if len(endpoints) != 2 or hub is None:
        endpoints = ['Stuttgart', 'Seville']
        hub = 'Manchester'
    
    orders = [
        [endpoints[0], hub, endpoints[1]],
        [endpoints[1], hub, endpoints[0]]
    ]
    
    constraint_stuttgart = (1, 6)
    chosen_order = None
    segments = None
    
    for order in orders:
        try:
            a = cities_info[order[0]]['required_days']
            b = cities_info[order[1]]['required_days']
            c = cities_info[order[2]]['required_days']
        except KeyError:
            continue
        
        if a + b + c - 2 != total_days:
            continue
        
        seg1 = (1, a)
        seg2 = (a, a + b - 1)
        seg3 = (a + b - 1, a + b + c - 2)
        
        if order[0] == 'Stuttgart':
            stuttgart_seg = seg1
        elif order[1] == 'Stuttgart':
            stuttgart_seg = seg2
        elif order[2] == 'Stuttgart':
            stuttgart_seg = seg3
        else:
            continue
        
        low, high = constraint_stuttgart
        start, end = stuttgart_seg
        if start <= high and end >= low:
            chosen_order = order
            segments = [seg1, seg2, seg3]
            break
    
    if chosen_order is None:
        result = {"itinerary": []}
    else:
        itinerary_list = []
        for i in range(3):
            start, end = segments[i]
            if start == end:
                day_range_str = f"Day {start}"
            else:
                day_range_str = f"Day {start}-{end}"
            itinerary_list.append({
                "day_range": day_range_str,
                "place": chosen_order[i]
            })
        result = {"itinerary": itinerary_list}
    
    print(json.dumps(result))

if __name__ == '__main__':
    main()