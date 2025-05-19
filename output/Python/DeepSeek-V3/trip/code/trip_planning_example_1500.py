import json
from itertools import permutations

def main():
    # Input parameters
    total_days = 28
    cities = {
        'Zurich': {'days': 2, 'constraints': [(7, 8)]},
        'Bucharest': {'days': 2, 'constraints': []},
        'Hamburg': {'days': 5, 'constraints': []},
        'Barcelona': {'days': 4, 'constraints': []},
        'Reykjavik': {'days': 5, 'constraints': [(9, 13)]},
        'Stuttgart': {'days': 5, 'constraints': []},
        'Stockholm': {'days': 2, 'constraints': []},
        'Tallinn': {'days': 4, 'constraints': []},
        'Milan': {'days': 5, 'constraints': [(3, 7)]},
        'London': {'days': 3, 'constraints': [(1, 3)]}
    }

    # Direct flights
    direct_flights = {
        'London': ['Hamburg', 'Reykjavik', 'Stuttgart', 'Barcelona', 'Bucharest', 'Stockholm', 'Milan', 'Zurich'],
        'Milan': ['Barcelona', 'Stockholm', 'Hamburg', 'Stuttgart', 'Reykjavik', 'Zurich', 'London'],
        'Reykjavik': ['London', 'Barcelona', 'Stuttgart', 'Stockholm', 'Milan', 'Zurich'],
        'Stockholm': ['Reykjavik', 'Hamburg', 'Stuttgart', 'Tallinn', 'Barcelona', 'Milan', 'Zurich'],
        'Hamburg': ['London', 'Stockholm', 'Milan', 'Stuttgart', 'Bucharest', 'Barcelona', 'Zurich'],
        'Stuttgart': ['Reykjavik', 'London', 'Stockholm', 'Milan', 'Hamburg', 'Barcelona'],
        'Barcelona': ['Milan', 'Reykjavik', 'London', 'Stockholm', 'Bucharest', 'Tallinn', 'Zurich', 'Hamburg', 'Stuttgart'],
        'Bucharest': ['Hamburg', 'London', 'Barcelona', 'Zurich'],
        'Zurich': ['Milan', 'London', 'Stockholm', 'Tallinn', 'Barcelona', 'Reykjavik', 'Bucharest', 'Hamburg'],
        'Tallinn': ['Stockholm', 'Barcelona', 'Zurich']
    }

    # Fixed constraints
    fixed_assignments = {}
    for city, info in cities.items():
        for start, end in info['constraints']:
            for day in range(start, end + 1):
                fixed_assignments[day] = city

    # Generate all possible city orders
    remaining_cities = [city for city in cities if not cities[city]['constraints']]
    city_permutations = permutations(remaining_cities)

    best_itinerary = None
    best_score = float('inf')

    for perm in city_permutations:
        itinerary = []
        current_city = None
        day = 1
        valid = True
        temp_assignments = fixed_assignments.copy()
        perm_list = list(perm)

        # Process fixed assignments first
        while day <= total_days:
            if day in temp_assignments:
                city = temp_assignments[day]
                if current_city != city:
                    if current_city is not None:
                        # Add flight
                        if city not in direct_flights[current_city]:
                            valid = False
                            break
                        itinerary.append({
                            'flying': f'Day {day}-{day}',
                            'from': current_city,
                            'to': city
                        })
                    current_city = city
                # Add stay
                end_day = day
                while end_day + 1 <= total_days and end_day + 1 in temp_assignments and temp_assignments[end_day + 1] == city:
                    end_day += 1
                itinerary.append({
                    'day_range': f'Day {day}-{end_day}',
                    'place': city
                })
                day = end_day + 1
            else:
                break

        if not valid:
            continue

        # Process remaining cities
        for city in perm_list:
            if cities[city]['days'] <= 0:
                continue
            if current_city is not None and city != current_city:
                if city not in direct_flights[current_city]:
                    valid = False
                    break
                itinerary.append({
                    'flying': f'Day {day}-{day}',
                    'from': current_city,
                    'to': city
                })
            current_city = city
            end_day = day + cities[city]['days'] - 1
            if end_day > total_days:
                valid = False
                break
            itinerary.append({
                'day_range': f'Day {day}-{end_day}',
                'place': city
            })
            day = end_day + 1
            if day > total_days:
                break

        if not valid or day <= total_days:
            continue

        # Check if all cities are visited
        visited_cities = set()
        for item in itinerary:
            if 'place' in item:
                visited_cities.add(item['place'])
            elif 'to' in item:
                visited_cities.add(item['to'])

        if len(visited_cities) != len(cities):
            continue

        # Score the itinerary (minimize flights)
        score = sum(1 for item in itinerary if 'flying' in item)
        if score < best_score:
            best_score = score
            best_itinerary = itinerary

    # Output the best itinerary
    print(json.dumps(best_itinerary, indent=2))

if __name__ == "__main__":
    main()