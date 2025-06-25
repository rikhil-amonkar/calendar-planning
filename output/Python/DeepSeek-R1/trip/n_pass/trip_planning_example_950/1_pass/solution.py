import json

def main():
    cities = ["Rome", "Mykonos", "Nice", "Riga", "Bucharest", "Munich", "Krakow"]
    durations = [4, 3, 3, 3, 4, 4, 2]
    
    undirected_edges = [
        ("Nice", "Riga"),
        ("Bucharest", "Munich"),
        ("Mykonos", "Munich"),
        ("Riga", "Bucharest"),
        ("Rome", "Nice"),
        ("Rome", "Munich"),
        ("Mykonos", "Nice"),
        ("Rome", "Mykonos"),
        ("Munich", "Krakow"),
        ("Rome", "Bucharest"),
        ("Nice", "Munich")
    ]
    directed_edges = [
        ("Riga", "Munich")
    ]
    
    allowed_flights = set()
    for a, b in undirected_edges:
        allowed_flights.add((a, b))
        allowed_flights.add((b, a))
    for a, b in directed_edges:
        allowed_flights.add((a, b))
    
    valid_route = True
    for i in range(len(cities) - 1):
        flight = (cities[i], cities[i+1])
        if flight not in allowed_flights:
            valid_route = False
            break
    
    if not valid_route:
        print("No valid itinerary found.")
        return
    
    itinerary = []
    current_start = 1
    for i in range(len(cities)):
        duration = durations[i]
        current_end = current_start + duration - 1
        if current_start == current_end:
            day_range_str = f"Day {current_start}"
        else:
            day_range_str = f"Day {current_start}-{current_end}"
        itinerary.append({"day_range": day_range_str, "place": cities[i]})
        current_start = current_end
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()