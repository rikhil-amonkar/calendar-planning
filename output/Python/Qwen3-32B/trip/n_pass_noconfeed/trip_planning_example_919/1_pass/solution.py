import itertools
import json

def main():
    # Define cities and durations
    cities = ['Vienna', 'Milan', 'Rome', 'Riga', 'Lisbon', 'Vilnius', 'Oslo']
    durations = {
        'Vienna': 4,
        'Milan': 2,
        'Rome': 3,
        'Riga': 2,
        'Lisbon': 3,
        'Vilnius': 4,
        'Oslo': 3
    }

    # Define direct flights
    direct_flights = set()
    pairs = [
        ('Riga', 'Oslo'),
        ('Rome', 'Oslo'),
        ('Vienna', 'Milan'),
        ('Vienna', 'Vilnius'),
        ('Vienna', 'Lisbon'),
        ('Riga', 'Milan'),
        ('Lisbon', 'Oslo'),
        ('Rome', 'Riga'),
        ('Rome', 'Lisbon'),
        ('Vienna', 'Riga'),
        ('Vienna', 'Rome'),
        ('Milan', 'Oslo'),
        ('Vienna', 'Oslo'),
        ('Vilnius', 'Oslo'),
        ('Riga', 'Vilnius'),
        ('Vilnius', 'Milan'),
        ('Riga', 'Lisbon'),
        ('Milan', 'Lisbon'),
    ]
    for a, b in pairs:
        direct_flights.add((a, b))
        direct_flights.add((b, a))

    # Generate permutations with Vienna as first city
    remaining = ['Milan', 'Rome', 'Riga', 'Lisbon', 'Vilnius', 'Oslo']
    for perm in itertools.permutations(remaining):
        sequence = ['Vienna'] + list(perm)
        # Check transitions
        valid = True
        for i in range(len(sequence) - 1):
            current = sequence[i]
            next_city = sequence[i + 1]
            if (current, next_city) not in direct_flights:
                valid = False
                break
        if not valid:
            continue

        # Calculate day ranges
        day_plan = []
        start_day = 1
        for city in sequence:
            dur = durations[city]
            end_day = start_day + dur - 1
            day_plan.append({
                'place': city,
                'start': start_day,
                'end': end_day
            })
            start_day = end_day  # Next city starts on the same day as previous ends

        # Check if the total days is 15
        if day_plan[-1]['end'] != 15:
            continue

        # Check Lisbon is 11-13
        lisbon_entry = None
        for entry in day_plan:
            if entry['place'] == 'Lisbon':
                lisbon_entry = entry
                break
        if lisbon_entry is None or lisbon_entry['start'] != 11 or lisbon_entry['end'] != 13:
            continue

        # Check Oslo is 13-15
        oslo_entry = None
        for entry in day_plan:
            if entry['place'] == 'Oslo':
                oslo_entry = entry
                break
        if oslo_entry is None or oslo_entry['start'] != 13 or oslo_entry['end'] != 15:
            continue

        # If all checks passed, build the itinerary
        itinerary = []
        for entry in day_plan:
            day_range = f"Day {entry['start']}-{entry['end']}"
            itinerary.append({'day_range': day_range, 'place': entry['place']})

        # Output as JSON
        print(json.dumps({'itinerary': itinerary}, indent=2))
        return

    # If no itinerary found
    print(json.dumps({'error': 'No valid itinerary found'}, indent=2))

if __name__ == '__main__':
    main()