import itertools
import json

def main():
    cities = ['Hamburg', 'Zurich', 'Helsinki', 'Bucharest', 'Split']
    durations = {
        'Hamburg': 2,
        'Zurich': 3,
        'Helsinki': 2,
        'Bucharest': 2,
        'Split': 7
    }
    flight_connections = {
        ('Zurich', 'Helsinki'),
        ('Hamburg', 'Bucharest'),
        ('Helsinki', 'Hamburg'),
        ('Zurich', 'Hamburg'),
        ('Zurich', 'Bucharest'),
        ('Zurich', 'Split'),
        ('Helsinki', 'Split'),
        ('Split', 'Hamburg'),
        # Reverse connections
        ('Helsinki', 'Zurich'),
        ('Bucharest', 'Hamburg'),
        ('Hamburg', 'Helsinki'),
        ('Hamburg', 'Zurich'),
        ('Bucharest', 'Zurich'),
        ('Split', 'Zurich'),
        ('Split', 'Helsinki'),
        ('Hamburg', 'Split'),
    }

    for perm in itertools.permutations(cities):
        valid_path = True
        for i in range(len(perm) - 1):
            current, next_city = perm[i], perm[i+1]
            if (current, next_city) not in flight_connections:
                valid_path = False
                break
        if not valid_path:
            continue

        day_ranges = []
        current_day = 1
        for city in perm:
            dur = durations[city]
            departure_day = current_day + dur - 1
            day_ranges.append({
                'city': city,
                'arrival': current_day,
                'departure': departure_day
            })
            current_day = departure_day

        if current_day != 12:
            continue

        # Check Zurich wedding (days 1-3)
        zurich_info = None
        for entry in day_ranges:
            if entry['city'] == 'Zurich':
                zurich_info = entry
                break
        has_wedding_day = False
        if zurich_info:
            z_arrival, z_departure = zurich_info['arrival'], zurich_info['departure']
            for day in range(1, 4):
                if z_arrival <= day <= z_departure:
                    has_wedding_day = True
                    break
        if not has_wedding_day:
            continue

        # Check Split conference (day 4 and 10)
        split_info = None
        for entry in day_ranges:
            if entry['city'] == 'Split':
                split_info = entry
                break
        if split_info:
            s_arrival, s_departure = split_info['arrival'], split_info['departure']
            if not (s_arrival <= 4 <= s_departure and s_arrival <= 10 <= s_departure):
                continue
        else:
            continue

        # Generate itinerary
        itinerary = []
        for entry in day_ranges:
            start_day = entry['arrival']
            end_day = entry['departure']
            day_range_str = f"Day {start_day}-{end_day}"
            itinerary.append({"day_range": day_range_str, "place": entry['city']})

        print(json.dumps({"itinerary": itinerary}, indent=2))
        return

    print(json.dumps({"error": "No valid itinerary found"}))

if __name__ == "__main__":
    main()