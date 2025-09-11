import json

def main():
    required_days = {
        'Krakow': 2,
        'Dubrovnik': 7,
        'Frankfurt': 3
    }
    flights = {
        'Dubrovnik': ['Frankfurt'],
        'Frankfurt': ['Dubrovnik', 'Krakow'],
        'Krakow': ['Frankfurt']
    }
    cities = list(required_days.keys())
    
    def generate_paths():
        all_paths = []
        def backtrack(current_path):
            if len(current_path) == 3:
                all_paths.append(current_path.copy())
                return
            if not current_path:
                for city in cities:
                    current_path.append(city)
                    backtrack(current_path)
                    current_path.pop()
            else:
                last_city = current_path[-1]
                for next_city in flights[last_city]:
                    if next_city not in current_path:
                        current_path.append(next_city)
                        backtrack(current_path)
                        current_path.pop()
        backtrack([])
        return all_paths
    
    paths = generate_paths()
    
    for path in paths:
        segments = []
        prev_end = 0
        for i, city in enumerate(path):
            if i == 0:
                start = 1
            else:
                start = prev_end
            duration = required_days[city]
            end = start + duration - 1
            segments.append((city, start, end))
            prev_end = end
        total_days = segments[-1][2]
        if total_days != 10:
            continue
        for city, start, end in segments:
            if city == 'Krakow' and start == 9 and end == 10:
                itinerary = []
                for city_name, s, e in segments:
                    day_range = f"Day {s}-{e}"
                    itinerary.append({"day_range": day_range, "place": city_name})
                output = {"itinerary": itinerary}
                print(json.dumps(output))
                return
    
    print(json.dumps({"error": "No valid itinerary found"}))

if __name__ == "__main__":
    main()