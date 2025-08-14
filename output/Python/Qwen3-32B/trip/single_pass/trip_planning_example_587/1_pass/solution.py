import json
from itertools import permutations

def main():
    # Define the cities and their required durations
    durations = {
        'Manchester': 3,
        'Istanbul': 7,
        'Venice': 7,
        'Krakow': 6,
        'Lyon': 2
    }

    # Define direct flight connections (undirected)
    direct_flights = [
        ('Manchester', 'Venice'),
        ('Manchester', 'Istanbul'),
        ('Manchester', 'Krakow'),
        ('Venice', 'Istanbul'),
        ('Venice', 'Lyon'),
        ('Istanbul', 'Krakow'),
        ('Lyon', 'Istanbul')
    ]

    # Create a set of frozensets for quick lookup
    flight_set = set()
    for a, b in direct_flights:
        flight_set.add(frozenset([a, b]))

    # Generate permutations of the remaining cities (after Manchester)
    remaining_cities = ['Istanbul', 'Venice', 'Krakow', 'Lyon']
    for perm in permutations(remaining_cities):
        order = ['Manchester'] + list(perm)
        # Check if all consecutive cities have direct flights
        valid = True
        for i in range(len(order) - 1):
            current = order[i]
            next_city = order[i + 1]
            if frozenset([current, next_city]) not in flight_set:
                valid = False
                break
        if not valid:
            continue

        # Calculate start and end days for each city
        start_days = {}
        end_days = {}
        current_start = 1
        for city in order:
            duration = durations[city]
            end_day = current_start + duration - 1
            start_days[city] = current_start
            end_days[city] = end_day
            current_start = end_day  # Next city starts on the same day as end of previous

        # Check total days is 21
        total_days = end_days[order[-1]]
        if total_days != 21:
            continue

        # Check Manchester's wedding is between day 1-3
        m_start = start_days['Manchester']
        m_end = end_days['Manchester']
        if not (m_start <= 3 and m_end >= 3):
            continue

        # Check Venice's workshop is between day 3-9
        v_start = start_days['Venice']
        v_end = end_days['Venice']
        if not (v_start <= 9 and v_end >= 3):
            continue

        # If all checks passed, build the itinerary
        itinerary = []
        for city in order:
            start = start_days[city]
            end = end_days[city]
            day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city})

        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
        return

    # If no valid itinerary found (though there should be one)
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()