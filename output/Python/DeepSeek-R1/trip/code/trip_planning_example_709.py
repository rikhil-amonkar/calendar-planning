import itertools
import json

def main():
    days_required = {
        'Helsinki': 4,
        'Valencia': 5,
        'Dubrovnik': 4,
        'Porto': 3,
        'Prague': 3,
        'Reykjavik': 4
    }

    flight_graph = {
        'Helsinki': {'Prague', 'Reykjavik', 'Dubrovnik'},
        'Prague': {'Helsinki', 'Valencia', 'Reykjavik'},
        'Valencia': {'Prague', 'Porto'},
        'Porto': {'Valencia'},
        'Reykjavik': {'Helsinki', 'Prague'},
        'Dubrovnik': {'Helsinki'}
    }

    cities = [city for city in days_required if city != 'Porto']
    valid_routes = []

    for perm in itertools.permutations(cities):
        route = list(perm) + ['Porto']
        valid = True
        for i in range(len(route) - 1):
            if route[i+1] not in flight_graph.get(route[i], set()):
                valid = False
                break
        if valid and len(set(route)) == 6:
            valid_routes.append(route)

    for route in valid_routes:
        current_start = 1
        itinerary = []
        for city in route:
            duration = days_required[city]
            end = current_start + duration - 1
            itinerary.append({
                'day_range': f"Day {current_start}-{end}" if current_start != end else f"Day {current_start}",
                'place': city
            })
            current_start = end

        if itinerary[-1]['place'] == 'Porto' and itinerary[-1]['day_range'] == "Day 16-18":
            print(json.dumps({"itinerary": itinerary}))
            return

    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()