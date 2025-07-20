import itertools
import json

def main():
    cities = {
        "Nice": 5,
        "Dublin": 7,
        "Krakow": 6,
        "Lyon": 4,
        "Frankfurt": 2
    }
    
    middle_cities = ["Dublin", "Krakow", "Lyon"]
    
    flight_pairs = [
        ("Nice", "Dublin"),
        ("Dublin", "Frankfurt"),
        ("Dublin", "Krakow"),
        ("Krakow", "Frankfurt"),
        ("Lyon", "Frankfurt"),
        ("Nice", "Frankfurt"),
        ("Nice", "Lyon"),
        ("Lyon", "Dublin")
    ]
    
    graph = {}
    for a, b in flight_pairs:
        if a not in graph:
            graph[a] = set()
        if b not in graph:
            graph[b] = set()
        graph[a].add(b)
        graph[b].add(a)
    
    found_perm = None
    for perm in itertools.permutations(middle_cities):
        A, B, C = perm
        if "Nice" in graph and A in graph["Nice"]:
            if A in graph and B in graph[A]:
                if B in graph and C in graph[B]:
                    if C in graph and "Frankfurt" in graph[C]:
                        found_perm = perm
                        break
    
    if found_perm is None:
        print(json.dumps({"itinerary": []}))
        return
    
    itinerary = [{"day_range": "Day 1-5", "place": "Nice"}]
    
    current_day = 5
    for city in found_perm:
        stay_days = cities[city]
        end_day = current_day + stay_days - 1
        itinerary.append({
            "day_range": f"Day {current_day}-{end_day}",
            "place": city
        })
        current_day = end_day
    
    itinerary.append({
        "day_range": f"Day {current_day}-{current_day + 1}",
        "place": "Frankfurt"
    })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()