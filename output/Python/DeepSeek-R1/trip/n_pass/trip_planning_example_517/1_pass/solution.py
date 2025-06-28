import json

def main():
    total_days = 19
    cities_order = ["Bucharest", "Warsaw", "Stuttgart", "Copenhagen", "Dubrovnik"]
    durations = {
        "Bucharest": 6,
        "Warsaw": 2,
        "Stuttgart": 7,
        "Copenhagen": 3,
        "Dubrovnik": 5
    }
    
    flight_connections = [
        ('Warsaw', 'Copenhagen'),
        ('Stuttgart', 'Copenhagen'),
        ('Warsaw', 'Stuttgart'),
        ('Bucharest', 'Copenhagen'),
        ('Bucharest', 'Warsaw'),
        ('Copenhagen', 'Dubrovnik')
    ]
    
    flight_pairs = set()
    for a, b in flight_connections:
        flight_pairs.add(frozenset([a, b]))
    
    for i in range(len(cities_order) - 1):
        city1 = cities_order[i]
        city2 = cities_order[i+1]
        pair = frozenset([city1, city2])
        if pair not in flight_pairs:
            raise ValueError(f"No flight connection between {city1} and {city2}")
    
    current_day = 1
    itinerary_list = []
    for city in cities_order:
        start = current_day
        end = start + durations[city] - 1
        if end > total_days:
            raise ValueError(f"Not enough days for {city}")
        itinerary_list.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })
        current_day = end
    
    if current_day != total_days:
        raise ValueError(f"Total days mismatch: ended at day {current_day}, expected {total_days}")
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()