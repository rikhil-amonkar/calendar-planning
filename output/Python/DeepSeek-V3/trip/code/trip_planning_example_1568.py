import json
from itertools import permutations

def main():
    # Input parameters
    cities = {
        'Prague': {'duration': 5, 'constraints': [{'range': (5, 9), 'event': 'annual show'}]},
        'Brussels': {'duration': 2, 'constraints': []},
        'Riga': {'duration': 2, 'constraints': [{'range': (15, 16), 'event': 'meet friends'}]},
        'Munich': {'duration': 2, 'constraints': []},
        'Seville': {'duration': 3, 'constraints': []},
        'Stockholm': {'duration': 2, 'constraints': [{'range': (16, 17), 'event': 'conference'}]},
        'Istanbul': {'duration': 2, 'constraints': []},
        'Amsterdam': {'duration': 3, 'constraints': []},
        'Vienna': {'duration': 5, 'constraints': [{'range': (1, 5), 'event': 'meet friend'}]},
        'Split': {'duration': 3, 'constraints': [{'range': (11, 13), 'event': 'visit relatives'}]}
    }

    direct_flights = {
        'Riga': ['Stockholm', 'Munich', 'Brussels', 'Amsterdam', 'Prague', 'Vienna', 'Istanbul'],
        'Stockholm': ['Riga', 'Brussels', 'Amsterdam', 'Vienna', 'Istanbul', 'Prague', 'Split', 'Munich'],
        'Brussels': ['Stockholm', 'Vienna', 'Munich', 'Istanbul', 'Prague', 'Riga', 'Seville'],
        'Munich': ['Istanbul', 'Amsterdam', 'Brussels', 'Prague', 'Stockholm', 'Split', 'Riga', 'Seville'],
        'Istanbul': ['Munich', 'Riga', 'Amsterdam', 'Stockholm', 'Brussels', 'Prague', 'Vienna'],
        'Prague': ['Split', 'Munich', 'Amsterdam', 'Brussels', 'Istanbul', 'Vienna', 'Stockholm', 'Riga'],
        'Amsterdam': ['Munich', 'Split', 'Stockholm', 'Seville', 'Riga', 'Vienna', 'Istanbul', 'Prague'],
        'Vienna': ['Brussels', 'Riga', 'Stockholm', 'Istanbul', 'Seville', 'Split', 'Amsterdam', 'Munich', 'Prague'],
        'Seville': ['Brussels', 'Amsterdam', 'Vienna', 'Munich'],
        'Split': ['Prague', 'Stockholm', 'Amsterdam', 'Munich', 'Vienna']
    }

    # Fixed constraints
    fixed_assignments = {
        1: 'Vienna',
        2: 'Vienna',
        3: 'Vienna',
        4: 'Vienna',
        5: 'Vienna',
        6: 'Prague',
        7: 'Prague',
        8: 'Prague',
        9: 'Prague',
        15: 'Riga',
        16: 'Stockholm',
        17: 'Stockholm',
        11: 'Split',
        12: 'Split',
        13: 'Split'
    }

    # Initialize schedule
    schedule = {}
    for day in range(1, 21):
        if day in fixed_assignments:
            schedule[day] = fixed_assignments[day]

    # Assign remaining cities
    remaining_cities = {city: data for city, data in cities.items() if city not in ['Vienna', 'Prague', 'Riga', 'Stockholm', 'Split']}
    remaining_days = [day for day in range(1, 21) if day not in fixed_assignments]

    # Try permutations to fit remaining cities
    city_order = list(remaining_cities.keys())
    best_schedule = None

    for perm in permutations(city_order):
        temp_schedule = schedule.copy()
        current_city = None
        remaining_days_copy = remaining_days.copy()
        success = True

        for city in perm:
            duration = remaining_cities[city]['duration']
            assigned = False

            for i in range(len(remaining_days_copy) - duration + 1):
                start_day = remaining_days_copy[i]
                end_day = start_day + duration - 1

                if end_day > 20:
                    continue

                # Check if all days in range are available
                valid = True
                for d in range(start_day, end_day + 1):
                    if d not in remaining_days_copy:
                        valid = False
                        break

                if not valid:
                    continue

                # Check flight connection
                if current_city is not None:
                    prev_city = temp_schedule[start_day - 1]
                    if city not in direct_flights.get(prev_city, []):
                        valid = False

                if valid:
                    for d in range(start_day, end_day + 1):
                        temp_schedule[d] = city
                        remaining_days_copy.remove(d)
                    current_city = city
                    assigned = True
                    break

            if not assigned:
                success = False
                break

        if success:
            best_schedule = temp_schedule
            break

    if not best_schedule:
        print("No valid itinerary found")
        return

    # Generate JSON output
    itinerary = []
    current_place = best_schedule[1]
    start_day = 1

    for day in range(2, 21):
        if best_schedule[day] != current_place:
            itinerary.append({'day_range': f'Day {start_day}-{day-1}', 'place': current_place})
            itinerary.append({'flying': f'Day {day-1}-{day}', 'from': current_place, 'to': best_schedule[day]})
            current_place = best_schedule[day]
            start_day = day

    itinerary.append({'day_range': f'Day {start_day}-20', 'place': current_place})

    print(json.dumps(itinerary, indent=2))

if __name__ == "__main__":
    main()