import json
from itertools import permutations

def main():
    # Input parameters
    total_days = 28
    cities = {
        'Copenhagen': {'duration': 5, 'constraints': [{'type': 'meet', 'day_range': (11, 15)}]},
        'Geneva': {'duration': 3, 'constraints': []},
        'Mykonos': {'duration': 2, 'constraints': [{'type': 'conference', 'day_range': (27, 28)}]},
        'Naples': {'duration': 4, 'constraints': [{'type': 'relatives', 'day_range': (5, 8)}]},
        'Prague': {'duration': 2, 'constraints': []},
        'Dubrovnik': {'duration': 3, 'constraints': []},
        'Athens': {'duration': 4, 'constraints': [{'type': 'workshop', 'day_range': (8, 11)}]},
        'Santorini': {'duration': 5, 'constraints': []},
        'Brussels': {'duration': 4, 'constraints': []},
        'Munich': {'duration': 5, 'constraints': []}
    }

    direct_flights = {
        'Copenhagen': ['Dubrovnik', 'Brussels', 'Naples', 'Prague', 'Athens', 'Geneva', 'Munich', 'Santorini'],
        'Geneva': ['Prague', 'Athens', 'Mykonos', 'Naples', 'Dubrovnik', 'Brussels', 'Munich', 'Santorini'],
        'Mykonos': ['Geneva', 'Naples', 'Athens', 'Munich'],
        'Naples': ['Dubrovnik', 'Athens', 'Mykonos', 'Copenhagen', 'Munich', 'Geneva', 'Santorini', 'Brussels'],
        'Prague': ['Geneva', 'Athens', 'Brussels', 'Copenhagen', 'Munich'],
        'Dubrovnik': ['Copenhagen', 'Athens', 'Naples', 'Geneva', 'Munich'],
        'Athens': ['Geneva', 'Dubrovnik', 'Mykonos', 'Naples', 'Prague', 'Santorini', 'Brussels', 'Munich', 'Copenhagen'],
        'Santorini': ['Geneva', 'Athens', 'Naples', 'Copenhagen'],
        'Brussels': ['Copenhagen', 'Naples', 'Prague', 'Athens', 'Munich', 'Geneva'],
        'Munich': ['Mykonos', 'Dubrovnik', 'Brussels', 'Athens', 'Geneva', 'Copenhagen', 'Prague', 'Naples']
    }

    # Generate all possible city orders
    city_names = list(cities.keys())
    possible_orders = permutations(city_names)

    valid_itineraries = []

    for order in possible_orders:
        itinerary = []
        current_day = 1
        valid = True

        # Check if the order satisfies all constraints
        for i, city in enumerate(order):
            city_info = cities[city]
            duration = city_info['duration']
            end_day = current_day + duration - 1

            # Check constraints
            for constraint in city_info.get('constraints', []):
                if constraint['type'] == 'meet':
                    meet_start, meet_end = constraint['day_range']
                    if not (current_day <= meet_end and end_day >= meet_start):
                        valid = False
                        break
                elif constraint['type'] == 'conference':
                    conf_start, conf_end = constraint['day_range']
                    if not (current_day <= conf_start and end_day >= conf_end):
                        valid = False
                        break
                elif constraint['type'] == 'relatives':
                    rel_start, rel_end = constraint['day_range']
                    if not (current_day <= rel_end and end_day >= rel_start):
                        valid = False
                        break
                elif constraint['type'] == 'workshop':
                    work_start, work_end = constraint['day_range']
                    if not (current_day <= work_start and end_day >= work_end):
                        valid = False
                        break
            if not valid:
                break

            # Check flight connections
            if i > 0:
                prev_city = order[i-1]
                if city not in direct_flights[prev_city]:
                    valid = False
                    break
                itinerary.append({'flying': f'Day {current_day-1}-{current_day-1}', 'from': prev_city, 'to': city})

            itinerary.append({'day_range': f'Day {current_day}-{end_day}', 'place': city})
            current_day = end_day + 1

            if current_day > total_days + 1:
                valid = False
                break

        if valid and current_day == total_days + 1:
            valid_itineraries.append(itinerary)

    # Select the first valid itinerary (can be optimized further)
    if valid_itineraries:
        selected_itinerary = valid_itineraries[0]
        print(json.dumps(selected_itinerary, indent=2))
    else:
        print(json.dumps([{'error': 'No valid itinerary found'}], indent=2))

if __name__ == "__main__":
    main()