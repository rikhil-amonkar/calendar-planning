import json
from itertools import product
from collections import defaultdict

def compute_itinerary(cities, durations, transitions, total_days):
    graph = defaultdict(list)
    for start, end in transitions:
        graph[start].append(end)

    itinerary = []
    current_city = None
    days = 0
    while days < total_days:
        for city, duration in durations.items():
            if duration > 0:
                if days + duration <= total_days:
                    current_city = city
                    itinerary.append({"day_range": f"Day {days + 1}-{days + duration}" if duration > 1 else f"Day {days + 1}", "place": city})
                    days += duration
                    durations[city] = 0
                    break

        if days < total_days:
            for next_city in graph[current_city]:
                if durations[next_city] > 0:
                    current_city = next_city
                    break
            else:
                # If we can't find a city to move to, just stay in the current city
                durations[current_city] = 0

    return {"itinerary": itinerary}

def main():
    cities = ["Nice", "Krakow", "Dublin", "Lyon", "Frankfurt"]
    durations = {
        "Nice": 5,
        "Krakow": 6,
        "Dublin": 7,
        "Lyon": 4,
        "Frankfurt": 2
    }
    transitions = [
        ("Nice", "Dublin"),
        ("Dublin", "Frankfurt"),
        ("Dublin", "Krakow"),
        ("Krakow", "Frankfurt"),
        ("Lyon", "Frankfurt"),
        ("Nice", "Frankfurt"),
        ("Lyon", "Dublin")
    ]
    total_days = 20

    result = compute_itinerary(cities, durations, transitions, total_days)
    print(json.dumps(result, indent=4))

if __name__ == "__main__":
    main()