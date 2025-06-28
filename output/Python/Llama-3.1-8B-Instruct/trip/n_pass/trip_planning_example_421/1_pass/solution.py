import json
from itertools import product
from collections import defaultdict

def compute_itinerary(cities, durations, transitions, total_days):
    graph = defaultdict(list)
    for start, end in transitions:
        graph[start].append(end)

    itinerary = []
    current_city = None
    for day in range(1, total_days + 1):
        for city, duration in durations.items():
            if duration == 0:
                continue
            if day <= duration:
                current_city = city
                itinerary.append({"day_range": f"Day {day}-{day + duration - 1}" if duration > 1 else f"Day {day}", "place": city})
                break

        if current_city is not None:
            for next_city in graph[current_city]:
                if next_city not in [city for city, duration in durations.items() if duration > 0]:
                    durations[next_city] = 1
                    current_city = next_city
                    break
        else:
            for city, duration in durations.items():
                if duration > 0:
                    durations[city] -= 1
                    current_city = city
                    break

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