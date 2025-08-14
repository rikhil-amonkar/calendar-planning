import json

def main():
    cities = {
        'Venice': 5,
        'Stockholm': 2,
        'Frankfurt': 4,
        'Florence': 4,
        'Barcelona': 2,
        'Stuttgart': 3,
        'Salzburg': 4
    }

    graph = {
        'Venice': ['Barcelona', 'Stuttgart', 'Frankfurt'],
        'Barcelona': ['Venice', 'Frankfurt', 'Florence', 'Stockholm', 'Stuttgart'],
        'Frankfurt': ['Venice', 'Barcelona', 'Florence', 'Salzburg', 'Stuttgart', 'Stockholm'],
        'Florence': ['Frankfurt', 'Barcelona'],
        'Stockholm': ['Barcelona', 'Frankfurt', 'Stuttgart'],
        'Stuttgart': ['Barcelona', 'Frankfurt', 'Stockholm', 'Venice'],
        'Salzburg': ['Frankfurt']
    }

    start_city = 'Venice'
    all_cities = list(cities.keys())
    remaining_cities = set(all_cities)
    remaining_cities.remove(start_city)

    def backtrack(current_path, remaining):
        if not remaining:
            return current_path.copy()
        current_city = current_path[-1]
        for neighbor in graph[current_city]:
            if neighbor in remaining:
                current_path.append(neighbor)
                remaining.remove(neighbor)
                result = backtrack(current_path, remaining)
                if result:
                    return result
                current_path.pop()
                remaining.add(neighbor)
        return None

    valid_path = backtrack([start_city], remaining_cities.copy())

    if not valid_path:
        print("No valid path found.")
        return

    itinerary = []
    current_day = 1
    for city in valid_path:
        duration = cities[city]
        end_day = current_day + duration - 1
        itinerary.append({
            "day_range": f"Day {current_day}-{end_day}",
            "place": city
        })
        current_day = end_day

    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()