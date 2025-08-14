import json

def main():
    durations = {
        'Reykjavik': 4,
        'Riga': 2,
        'Oslo': 3,
        'Lyon': 5,
        'Dubrovnik': 2,
        'Madrid': 2,
        'Warsaw': 4,
        'London': 3
    }

    flights = {
        'Reykjavik': ['Madrid', 'Warsaw', 'Oslo', 'London'],
        'Riga': ['Warsaw', 'Oslo'],
        'Oslo': ['Riga', 'Dubrovnik', 'Lyon', 'London', 'Reykjavik', 'Warsaw', 'Madrid'],
        'Lyon': ['Oslo', 'London', 'Madrid'],
        'Dubrovnik': ['Madrid'],
        'Madrid': ['Dubrovnik', 'Oslo', 'Lyon', 'London', 'Warsaw', 'Reykjavik'],
        'Warsaw': ['Reykjavik', 'Riga', 'London', 'Oslo', 'Madrid'],
        'London': ['Lyon', 'Madrid', 'Warsaw', 'Oslo', 'Reykjavik']
    }

    cities = list(durations.keys())

    def compute_start_days(path):
        start_days = [0] * len(path)
        start_days[0] = 1
        for i in range(1, len(path)):
            prev_city = path[i - 1]
            start_days[i] = start_days[i - 1] + durations[prev_city] - 1
        return start_days

    def find_valid_path(current_path):
        if len(current_path) == 8:
            start_days = compute_start_days(current_path)
            try:
                riga_index = current_path.index('Riga')
                if start_days[riga_index] != 4:
                    return None
            except ValueError:
                return None
            try:
                dubrovnik_index = current_path.index('Dubrovnik')
                if start_days[dubrovnik_index] != 7:
                    return None
            except ValueError:
                return None
            return current_path
        current_city = current_path[-1]
        for neighbor in flights[current_city]:
            if neighbor not in current_path:
                new_path = current_path + [neighbor]
                result = find_valid_path(new_path)
                if result is not None:
                    return result
        return None

    for start_city in cities:
        path = [start_city]
        valid_path = find_valid_path(path)
        if valid_path is not None:
            break
    else:
        print("No valid path found")
        return

    start_days = compute_start_days(valid_path)
    itinerary = []
    for i, city in enumerate(valid_path):
        start = start_days[i]
        duration = durations[city]
        end = start + duration - 1
        day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})

    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()