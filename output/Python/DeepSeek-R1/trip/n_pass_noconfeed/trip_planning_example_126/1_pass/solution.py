import json

def main():
    total_days = 11
    city_days = {
        "Seville": 6,
        "Paris": 2,
        "Krakow": 5
    }
    workshop_city = "Krakow"
    workshop_min_day = 1
    workshop_max_day = 5
    direct_flights = [("Krakow", "Paris"), ("Paris", "Seville")]
    
    graph = {}
    for a, b in direct_flights:
        graph.setdefault(a, []).append(b)
        graph.setdefault(b, []).append(a)
    
    all_cities = list(city_days.keys())
    other_cities = [city for city in all_cities if city != workshop_city]
    
    path = None
    if workshop_city in graph:
        for next_city in graph[workshop_city]:
            last_city_list = [city for city in other_cities if city != next_city]
            if len(last_city_list) == 1:
                last_city = last_city_list[0]
                if next_city in graph and last_city in graph[next_city]:
                    path = [workshop_city, next_city, last_city]
                    break
    
    if path is None:
        print(json.dumps({"itinerary": []}))
        return
    
    n = len(path)
    starts = [0] * n
    ends = [0] * n
    
    starts[0] = 1
    ends[0] = starts[0] + city_days[path[0]] - 1
    
    for i in range(1, n):
        starts[i] = ends[i-1]
        ends[i] = starts[i] + city_days[path[i]] - 1
    
    if ends[-1] > total_days:
        print(json.dumps({"itinerary": []}))
        return
    
    try:
        idx = path.index(workshop_city)
        if starts[idx] > workshop_min_day or ends[idx] < workshop_max_day:
            print(json.dumps({"itinerary": []}))
            return
    except ValueError:
        print(json.dumps({"itinerary": []}))
        return
    
    itinerary = []
    for i in range(n):
        day_range_str = f"Day {starts[i]}-{ends[i]}"
        itinerary.append({"day_range": day_range_str, "place": path[i]})
    
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()