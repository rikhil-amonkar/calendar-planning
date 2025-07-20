import json

def main():
    # Define the fixed itinerary segments based on constraints
    itinerary_stays = [
        {"city": "Istanbul", "start_day": 1, "end_day": 5},
        {"city": "Brussels", "start_day": 5, "end_day": 7},
        {"city": "Milan", "start_day": 7, "end_day": 10},
        {"city": "Split", "start_day": 10, "end_day": 13},
        {"city": "Helsinki", "start_day": 13, "end_day": 15},
        {"city": "Dubrovnik", "start_day": 15, "end_day": 16},
        {"city": "Frankfurt", "start_day": 16, "end_day": 18},
        {"city": "Vilnius", "start_day": 18, "end_day": 22}
    ]
    
    # Build the flight graph from the given connections
    bidirectional_edges = [
        ('Milan', 'Frankfurt'),
        ('Split', 'Frankfurt'),
        ('Milan', 'Split'),
        ('Brussels', 'Vilnius'),
        ('Brussels', 'Helsinki'),
        ('Istanbul', 'Brussels'),
        ('Milan', 'Vilnius'),
        ('Brussels', 'Milan'),
        ('Istanbul', 'Helsinki'),
        ('Helsinki', 'Vilnius'),
        ('Helsinki', 'Dubrovnik'),
        ('Split', 'Vilnius'),
        ('Istanbul', 'Milan'),
        ('Helsinki', 'Frankfurt'),
        ('Istanbul', 'Vilnius'),
        ('Split', 'Helsinki'),
        ('Milan', 'Helsinki'),
        ('Istanbul', 'Frankfurt'),
        ('Dubrovnik', 'Frankfurt'),
        ('Frankfurt', 'Vilnius')
    ]
    directed_edges = [
        ('Dubrovnik', 'Istanbul'),
        ('Brussels', 'Frankfurt')
    ]
    
    flight_graph = {}
    for a, b in bidirectional_edges:
        if a not in flight_graph:
            flight_graph[a] = set()
        if b not in flight_graph:
            flight_graph[b] = set()
        flight_graph[a].add(b)
        flight_graph[b].add(a)
    
    for a, b in directed_edges:
        if a not in flight_graph:
            flight_graph[a] = set()
        flight_graph[a].add(b)
    
    # Verify flight connections between consecutive cities in the itinerary
    for i in range(len(itinerary_stays) - 1):
        from_city = itinerary_stays[i]["city"]
        to_city = itinerary_stays[i+1]["city"]
        
        if from_city not in flight_graph:
            raise ValueError(f"No flight connections from {from_city}")
        if to_city not in flight_graph[from_city]:
            raise ValueError(f"No direct flight from {from_city} to {to_city}")
    
    # Convert to the required JSON output format
    itinerary_list = []
    for stay in itinerary_stays:
        start = stay["start_day"]
        end = stay["end_day"]
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        itinerary_list.append({"day_range": day_range, "place": stay["city"]})
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()