import json

def main():
    total_days = 15
    cities = {
        'Manchester': {'days': 7, 'event': (1, 7)},
        'Stuttgart': {'days': 5, 'event': (11, 15)},
        'Madrid': {'days': 4},
        'Vienna': {'days': 2}
    }
    
    direct_flights = [
        ('Vienna', 'Stuttgart'),
        ('Manchester', 'Vienna'),
        ('Madrid', 'Vienna'),
        ('Manchester', 'Stuttgart'),
        ('Manchester', 'Madrid')
    ]
    
    graph = {}
    for a, b in direct_flights:
        if a not in graph:
            graph[a] = set()
        if b not in graph:
            graph[b] = set()
        graph[a].add(b)
        graph[b].add(a)
    
    orders = [
        ['Madrid', 'Vienna'],
        ['Vienna', 'Madrid']
    ]
    
    valid_order = None
    for order in orders:
        city1, city2 = order
        if 'Manchester' in graph and city1 in graph['Manchester']:
            if city1 in graph and city2 in graph[city1]:
                if city2 in graph and 'Stuttgart' in graph[city2]:
                    valid_order = order
                    break
    
    itinerary_segments = []
    itinerary_segments.append({'day_range': f"Day 1-7", 'place': 'Manchester'})
    
    if valid_order:
        city1, city2 = valid_order
        days_city1 = cities[city1]['days']
        start_city1 = 7
        end_city1 = start_city1 + days_city1 - 1
        itinerary_segments.append({'day_range': f"Day {start_city1}-{end_city1}", 'place': city1})
        
        days_city2 = cities[city2]['days']
        start_city2 = end_city1
        end_city2 = start_city2 + days_city2 - 1
        itinerary_segments.append({'day_range': f"Day {start_city2}-{end_city2}", 'place': city2})
        
        itinerary_segments.append({'day_range': "Day 11-15", 'place': 'Stuttgart'})
    else:
        raise ValueError("No valid itinerary found")
    
    result = {'itinerary': itinerary_segments}
    print(json.dumps(result))

if __name__ == '__main__':
    main()