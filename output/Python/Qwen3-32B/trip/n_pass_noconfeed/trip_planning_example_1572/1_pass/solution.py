import json
from collections import defaultdict

def main():
    # Define the cities and their required durations
    durations = {
        'Berlin': 2,
        'Paris': 5,
        'Lyon': 3,
        'Riga': 2,
        'Stockholm': 3,
        'Zurich': 5,
        'Nice': 2,
        'Seville': 3,
        'Milan': 3,
        'Naples': 4
    }

    # Define direct flights as adjacency list
    direct_flights = [
        ('Paris', 'Stockholm'),
        ('Seville', 'Paris'),
        ('Naples', 'Zurich'),
        ('Nice', 'Riga'),
        ('Berlin', 'Milan'),
        ('Paris', 'Zurich'),
        ('Paris', 'Nice'),
        ('Milan', 'Paris'),
        ('Milan', 'Riga'),
        ('Paris', 'Lyon'),
        ('Milan', 'Naples'),
        ('Paris', 'Riga'),
        ('Berlin', 'Riga'),
        ('Berlin', 'Milan'),
        ('Stockholm', 'Riga'),
        ('Nice', 'Zurich'),
        ('Milan', 'Zurich'),
        ('Lyon', 'Nice'),
        ('Zurich', 'Stockholm'),
        ('Zurich', 'Riga'),
        ('Berlin', 'Naples'),
        ('Milan', 'Stockholm'),
        ('Berlin', 'Zurich'),
        ('Milan', 'Seville'),
        ('Paris', 'Naples'),
        ('Berlin', 'Riga'),
        ('Nice', 'Stockholm'),
        ('Berlin', 'Nice'),
        ('Nice', 'Naples')
    ]

    adj = defaultdict(list)
    for a, b in direct_flights:
        adj[a].append(b)
        adj[b].append(a)

    # List of all cities
    all_cities = list(durations.keys())

    # Function to check if a path is valid
    def is_valid_path(path):
        if len(set(path)) != len(path):
            return False
        if path[0] != 'Berlin':
            return False
        if path[-1] != 'Stockholm':
            return False
        for i in range(len(path) - 1):
            if path[i+1] not in adj[path[i]]:
                return False
        return True

    # Backtracking to find valid path
    def backtrack(current_path, visited):
        if len(current_path) == 10:
            if is_valid_path(current_path):
                return current_path
            return None

        current_city = current_path[-1]
        for neighbor in adj[current_city]:
            if neighbor not in visited:
                new_path = current_path + [neighbor]
                new_visited = visited | {neighbor}
                result = backtrack(new_path, new_visited)
                if result:
                    return result
        return None

    # Start backtracking with Berlin
    initial_path = ['Berlin']
    visited = {'Berlin'}
    itinerary = backtrack(initial_path, visited)

    if not itinerary:
        print("No valid itinerary found.")
        return

    # Compute start days for each city in the itinerary
    start_days = [1]  # start day of first city (Berlin) is 1
    for i in range(1, len(itinerary)):
        prev_duration = durations[itinerary[i-1]]
        start_day = start_days[i-1] + prev_duration - 1
        start_days.append(start_day)

    # Check if Nice is at start day 12 and Stockholm at start day 21
    nice_index = itinerary.index('Nice') if 'Nice' in itinerary else -1
    stockholm_index = itinerary.index('Stockholm') if 'Stockholm' in itinerary else -1

    if nice_index != -1 and start_days[nice_index] != 12:
        print("Invalid itinerary: Nice not at start day 12.")
        return

    if stockholm_index != -1 and start_days[stockholm_index] != 21:
        print("Invalid itinerary: Stockholm not at start day 21.")
        return

    # Generate the day ranges
    result = []
    for i, city in enumerate(itinerary):
        start = start_days[i]
        duration = durations[city]
        end = start + duration - 1
        day_range = f"Day {start}-{end}"
        result.append({"day_range": day_range, "place": city})

    print(json.dumps({"itinerary": result}))

if __name__ == "__main__":
    main()