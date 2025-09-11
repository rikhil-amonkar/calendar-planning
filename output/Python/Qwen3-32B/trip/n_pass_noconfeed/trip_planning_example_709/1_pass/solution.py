import json

def main():
    cities_days = {
        "Dubrovnik": 4,
        "Helsinki": 4,
        "Reykjavik": 4,
        "Prague": 3,
        "Valencia": 5,
        "Porto": 3
    }

    adj = {
        "Dubrovnik": ["Helsinki"],
        "Helsinki": ["Dubrovnik", "Prague", "Reykjavik"],
        "Reykjavik": ["Helsinki", "Prague"],
        "Prague": ["Helsinki", "Valencia", "Reykjavik"],
        "Valencia": ["Prague", "Porto"],
        "Porto": ["Valencia"]
    }

    all_paths = []
    cities = list(cities_days.keys())

    def find_hamiltonian_paths(start, path, visited):
        if len(path) == len(cities):
            return [path.copy()]
        paths = []
        for neighbor in adj[start]:
            if neighbor not in visited:
                path.append(neighbor)
                visited.add(neighbor)
                subpaths = find_hamiltonian_paths(neighbor, path, visited)
                for subpath in subpaths:
                    paths.append(subpath)
                path.pop()
                visited.remove(neighbor)
        return paths

    for start_city in cities:
        path = [start_city]
        visited = {start_city}
        paths = find_hamiltonian_paths(start_city, path, visited)
        all_paths.extend(paths)

    valid_paths = []
    for path in all_paths:
        day_ranges = []
        current_start = 1
        current_city = path[0]
        duration = cities_days[current_city]
        end_day = current_start + duration - 1
        day_ranges.append((current_start, end_day, current_city))
        for i in range(1, len(path)):
            current_start = end_day
            current_city = path[i]
            duration = cities_days[current_city]
            end_day = current_start + duration - 1
            day_ranges.append((current_start, end_day, current_city))
        total_days = end_day
        if total_days != 18:
            continue
        porto_days = None
        for start, end, city in day_ranges:
            if city == "Porto":
                porto_days = (start, end)
                break
        if porto_days:
            porto_start, porto_end = porto_days
            if porto_start <= 18 and porto_end >= 16:
                valid_paths.append((path, day_ranges))

    if valid_paths:
        path, day_ranges = valid_paths[0]
        itinerary = []
        for start, end, city in day_ranges:
            day_range_str = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range_str, "place": city})
        print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()