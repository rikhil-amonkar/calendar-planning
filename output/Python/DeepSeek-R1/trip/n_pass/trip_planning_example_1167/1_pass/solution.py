import json

def main():
    total_days = 21
    cities_order = ["Mykonos", "Naples", "Venice", "Istanbul", "Dublin", "Frankfurt", "Krakow", "Brussels"]
    durations = {
        "Mykonos": 4,
        "Naples": 4,
        "Venice": 3,
        "Istanbul": 3,
        "Dublin": 5,
        "Frankfurt": 3,
        "Krakow": 4,
        "Brussels": 2
    }
    
    flight_pairs = [
        ("Dublin", "Brussels"),
        ("Mykonos", "Naples"),
        ("Venice", "Istanbul"),
        ("Frankfurt", "Krakow"),
        ("Naples", "Dublin"),
        ("Krakow", "Brussels"),
        ("Naples", "Istanbul"),
        ("Naples", "Brussels"),
        ("Istanbul", "Frankfurt"),
        ("Brussels", "Frankfurt"),
        ("Istanbul", "Krakow"),
        ("Istanbul", "Brussels"),
        ("Venice", "Frankfurt"),
        ("Naples", "Frankfurt"),
        ("Dublin", "Krakow"),
        ("Venice", "Brussels"),
        ("Naples", "Venice"),
        ("Istanbul", "Dublin"),
        ("Venice", "Dublin"),
        ("Dublin", "Frankfurt")
    ]
    
    canonical_flights = set()
    for a, b in flight_pairs:
        key = (min(a, b), max(a, b))
        canonical_flights.add(key)
    
    for i in range(len(cities_order) - 1):
        city1 = cities_order[i]
        city2 = cities_order[i+1]
        key = (min(city1, city2), max(city1, city2))
        if key not in canonical_flights:
            raise RuntimeError(f"No direct flight between {city1} and {city2} found.")
    
    start = 1
    itinerary_list = []
    for city in cities_order:
        duration = durations[city]
        end = start + duration - 1
        itinerary_list.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })
        start = end
    
    if end != total_days:
        raise RuntimeError(f"Itinerary ends at day {end}, but should end at day {total_days}.")
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()