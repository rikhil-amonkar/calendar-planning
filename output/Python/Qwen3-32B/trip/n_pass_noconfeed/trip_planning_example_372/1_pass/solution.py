import json

def main():
    # Define allowed flights
    allowed_flights = {
        'Porto': ['Stuttgart', 'Seville', 'Madrid'],
        'Seville': ['Porto', 'Madrid'],
        'Madrid': ['Porto', 'Seville'],
        'Stuttgart': ['Porto']
    }

    # Define required durations
    city_durations = {
        'Seville': 2,
        'Stuttgart': 7,
        'Porto': 3,
        'Madrid': 4
    }

    # Find all valid paths of 4 cities ending with Stuttgart
    def find_valid_paths():
        valid_paths = []
        for start_city in allowed_flights:
            for path in dfs(allowed_flights, [start_city], 3):
                if path[-1] == 'Stuttgart' and len(set(path)) == 4:
                    valid_paths.append(path)
        return valid_paths

    def dfs(allowed_flights, current_path, remaining_steps):
        if remaining_steps == 0:
            return [current_path.copy()]
        current_city = current_path[-1]
        next_cities = allowed_flights[current_city]
        valid_paths = []
        for next_city in next_cities:
            if next_city in current_path:
                continue
            current_path.append(next_city)
            valid_paths.extend(dfs(allowed_flights, current_path, remaining_steps - 1))
            current_path.pop()
        return valid_paths

    valid_paths = find_valid_paths()

    # Check each valid path
    for path in valid_paths:
        # Compute day ranges
        current_day = 1
        itinerary_plan = []
        valid = True
        for i, city in enumerate(path):
            duration = city_durations[city]
            if i < len(path) - 1:  # not last city
                start_day = current_day
                end_day = current_day + duration - 1
                itinerary_plan.append((start_day, end_day, city))
                current_day = end_day
            else:  # last city (Stuttgart)
                start_day = current_day
                end_day = current_day + duration - 1
                itinerary_plan.append((start_day, end_day, city))
        # Check if Stuttgart starts on day 7 and ends on 13
        stuttgart_start, stuttgart_end, _ = itinerary_plan[-1]
        if stuttgart_start != 7 or stuttgart_end != 13:
            continue
        # Check if Madrid's stay includes days between 1-4
        madrid_days = None
        for start, end, city in itinerary_plan:
            if city == 'Madrid':
                madrid_days = (start, end)
                break
        if madrid_days is None:
            continue
        # Check if any day in Madrid is between 1-4
        if madrid_days[0] > 4:
            continue
        # Valid path found
        # Generate the JSON itinerary
        json_itinerary = []
        for start, end, city in itinerary_plan:
            day_range = f"Day {start}-{end}"
            json_itinerary.append({"day_range": day_range, "place": city})
        print(json.dumps({"itinerary": json_itinerary}))
        return

    # If no valid path found
    print(json.dumps({"error": "No valid itinerary found"}))

if __name__ == "__main__":
    main()