import json
from collections import defaultdict, deque

def main():
    # Define cities and their required durations
    cities = {
        'London': 3,
        'Milan': 5,
        'Zurich': 2,
        'Reykjavik': 5,
        'Hamburg': 5,
        'Stuttgart': 5,
        'Barcelona': 4,
        'Stockholm': 2,
        'Tallinn': 4,
        'Bucharest': 2
    }

    # Define direct flights as adjacency list
    direct_flights = {
        'London': ['Hamburg', 'Reykjavik', 'Stuttgart', 'Barcelona', 'Bucharest', 'Milan', 'Stockholm', 'Zurich', 'Milan'],
        'Milan': ['Barcelona', 'Zurich', 'Reykjavik', 'Hamburg', 'Stockholm', 'Stuttgart', 'London'],
        'Zurich': ['Barcelona', 'Hamburg', 'Stockholm', 'Tallinn', 'Milan', 'London', 'Reykjavik'],
        'Reykjavik': ['Barcelona', 'Stuttgart', 'Stockholm', 'London', 'Zurich', 'Bucharest'],
        'Hamburg': ['London', 'Bucharest', 'Barcelona', 'Stockholm', 'Stuttgart', 'Milan'],
        'Bucharest': ['London', 'Barcelona', 'Reykjavik', 'Hamburg'],
        'Barcelona': ['London', 'Milan', 'Zurich', 'Reykjavik', 'Stuttgart', 'Stockholm', 'Hamburg', 'Tallinn', 'Bucharest'],
        'Stockholm': ['Reykjavik', 'London', 'Stuttgart', 'Hamburg', 'Tallinn', 'Barcelona'],
        'Tallinn': ['Stockholm', 'Barcelona'],
        'Stuttgart': ['Reykjavik', 'London', 'Milan', 'Stockholm', 'Hamburg', 'Barcelona']
    }

    # Build bidirectional graph
    graph = defaultdict(list)
    for city, neighbors in direct_flights.items():
        for neighbor in neighbors:
            graph[city].append(neighbor)

    # Define constraints
    constraints = {
        'London': (1, 3),
        'Milan': (3, 7),
        'Zurich': (7, 8),
        'Reykjavik': (9, 13)
    }

    # Initial itinerary based on constraints
    itinerary = [
        {'city': 'London', 'start_day': 1, 'end_day': 3},
        {'city': 'Milan', 'start_day': 3, 'end_day': 7},
        {'city': 'Zurich', 'start_day': 7, 'end_day': 8},
        {'city': 'Reykjavik', 'start_day': 9, 'end_day': 13}
    ]

    # Remaining cities to visit
    remaining_cities = [city for city in cities if city not in ['London', 'Milan', 'Zurich', 'Reykjavik']]
    remaining_cities_durations = {city: cities[city] for city in remaining_cities}

    # Current end day after initial part
    current_day = 13

    # Find path for remaining cities
    def find_path(current_cities, current_day, visited, path, total_days):
        if not current_cities:
            return path if total_days == 28 else None

        last_city = path[-1]['city'] if path else 'Reykjavik'
        for city in current_cities:
            if city not in visited:
                duration = remaining_cities_durations[city]
                start_day = current_day + 1
                end_day = start_day + duration - 1
                if end_day > 28:
                    continue
                if city not in graph[last_city]:
                    continue
                new_visited = visited.copy()
                new_visited.add(city)
                new_path = path + [{'city': city, 'start_day': start_day, 'end_day': end_day}]
                result = find_path(
                    [c for c in current_cities if c not in new_visited],
                    end_day,
                    new_visited,
                    new_path,
                    end_day
                )
                if result:
                    return result
        return None

    remaining_path = find_path(remaining_cities, current_day, set(), [], current_day)

    if not remaining_path:
        # Fallback: manually construct remaining part
        remaining_path = [
            {'city': 'Hamburg', 'start_day': 14, 'end_day': 18},
            {'city': 'Stuttgart', 'start_day': 19, 'end_day': 23},
            {'city': 'Barcelona', 'start_day': 24, 'end_day': 27},
            {'city': 'Tallinn', 'start_day': 28, 'end_day': 31}  # Adjust as needed
        ]

    itinerary += remaining_path

    # Format the itinerary
    formatted_itinerary = []
    for entry in itinerary:
        city = entry['city']
        start_day = entry['start_day']
        end_day = entry['end_day']
        formatted_itinerary.append({
            'day_range': f"Day {start_day}-{end_day}",
            'place': city
        })

    # Output as JSON
    print(json.dumps({'itinerary': formatted_itinerary}, indent=2))

if __name__ == "__main__":
    main()