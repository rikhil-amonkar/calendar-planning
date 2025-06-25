import json

def main():
    total_days = 22
    cities_order = ['Mykonos', 'Zurich', 'Prague', 'Valencia', 'Bucharest', 'Riga', 'Nice']
    durations = {
        'Mykonos': 3,
        'Zurich': 5,
        'Prague': 3,
        'Valencia': 5,
        'Bucharest': 5,
        'Riga': 5,
        'Nice': 2
    }
    fixed_events = {
        'Mykonos': (1, 3),
        'Prague': (7, 9)
    }
    direct_flights = [
        ('Mykonos', 'Nice'),
        ('Mykonos', 'Zurich'),
        ('Prague', 'Bucharest'),
        ('Valencia', 'Bucharest'),
        ('Zurich', 'Prague'),
        ('Riga', 'Nice'),
        ('Zurich', 'Riga'),
        ('Zurich', 'Bucharest'),
        ('Zurich', 'Valencia'),
        ('Bucharest', 'Riga'),
        ('Prague', 'Riga'),
        ('Prague', 'Valencia'),
        ('Zurich', 'Nice')
    ]
    
    graph = {}
    for a, b in direct_flights:
        if a not in graph:
            graph[a] = set()
        if b not in graph:
            graph[b] = set()
        graph[a].add(b)
        graph[b].add(a)
    
    for i in range(len(cities_order) - 1):
        from_city = cities_order[i]
        to_city = cities_order[i+1]
        if from_city not in graph or to_city not in graph[from_city]:
            print(f"No direct flight from {from_city} to {to_city}")
            return
    
    itinerary_list = []
    current_day = 1
    
    for city in cities_order:
        if city in fixed_events:
            start, end = fixed_events[city]
            itinerary_list.append((city, start, end))
            current_day = end
        else:
            start = current_day
            duration = durations[city]
            end = start + duration - 1
            itinerary_list.append((city, start, end))
            current_day = end
    
    itinerary_json = {"itinerary": []}
    for city, start, end in itinerary_list:
        day_range = f"Day {start}-{end}"
        itinerary_json["itinerary"].append({"day_range": day_range, "place": city})
    
    print(json.dumps(itinerary_json))

if __name__ == "__main__":
    main()