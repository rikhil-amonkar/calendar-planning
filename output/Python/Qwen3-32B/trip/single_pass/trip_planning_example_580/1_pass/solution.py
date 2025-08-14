import json

def main():
    required_durations = {
        'Geneva': 7,
        'Paris': 6,
        'Porto': 7,
        'Oslo': 5,
        'Reykjavik': 2
    }

    allowed_flights = {
        'Paris': ['Oslo', 'Reykjavik', 'Porto', 'Geneva'],
        'Geneva': ['Paris', 'Oslo', 'Porto'],
        'Porto': ['Paris', 'Oslo', 'Geneva'],
        'Oslo': ['Paris', 'Geneva', 'Reykjavik', 'Porto'],
        'Reykjavik': ['Paris', 'Oslo']
    }

    # The order of cities in the itinerary, determined based on constraints
    itinerary_order = ['Geneva', 'Paris', 'Porto', 'Oslo', 'Reykjavik']

    # Check transitions between consecutive cities
    for i in range(len(itinerary_order) - 1):
        current_city = itinerary_order[i]
        next_city = itinerary_order[i + 1]
        if next_city not in allowed_flights[current_city]:
            raise ValueError(f"Invalid transition from {current_city} to {next_city}")

    # Compute the itinerary day ranges
    current_day = 1
    itinerary = []
    for city in itinerary_order:
        duration = required_durations[city]
        end_day = current_day + duration - 1
        day_range = f"Day {current_day}-{end_day}"
        itinerary.append({'day_range': day_range, 'place': city})
        current_day = end_day

    # Check Oslo's visit is within day 19-23
    for entry in itinerary:
        if entry['place'] == 'Oslo':
            start_day_str, end_day_str = entry['day_range'].split(' ')[1].split('-')
            start_day = int(start_day_str[3:])
            end_day = int(end_day_str)
            if not (19 <= start_day and end_day <= 23):
                raise ValueError("Oslo visit not within required days")

    # Check total days
    total_days_computed = sum(required_durations.values()) - (len(itinerary_order) - 1)
    if total_days_computed != 23:
        raise ValueError("Total days do not match 23")

    # Check Geneva has days 1 and 7
    geneva_entry = next(entry for entry in itinerary if entry['place'] == 'Geneva')
    geneva_days = geneva_entry['day_range'].split('-')
    start = int(geneva_days[0][3:])
    end = int(geneva_days[1])
    if start != 1 or end < 7:
        raise ValueError("Geneva does not include day 1 and 7")

    # Output JSON
    output = {'itinerary': itinerary}
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()