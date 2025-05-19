import json
from itertools import permutations

def find_itinerary():
    # Input parameters
    total_days = 12
    city_days = {
        'Split': 2,
        'Helsinki': 2,
        'Reykjavik': 3,
        'Vilnius': 3,
        'Geneva': 6
    }
    constraints = {
        'Reykjavik': (10, 12),
        'Vilnius': (7, 9)
    }
    direct_flights = {
        'Split': ['Helsinki', 'Geneva', 'Vilnius'],
        'Helsinki': ['Split', 'Geneva', 'Reykjavik', 'Vilnius'],
        'Geneva': ['Split', 'Helsinki'],
        'Reykjavik': ['Helsinki'],
        'Vilnius': ['Helsinki', 'Split']
    }

    # Generate all possible city orders
    cities = list(city_days.keys())
    possible_orders = permutations(cities)

    valid_itineraries = []

    for order in possible_orders:
        itinerary = []
        current_day = 1
        prev_city = None
        valid = True

        for i, city in enumerate(order):
            # Check if we can stay in this city for required days
            required_days = city_days[city]
            end_day = current_day + required_days - 1

            # Check constraints
            if city in constraints:
                constraint_start, constraint_end = constraints[city]
                if not (current_day <= constraint_end and end_day >= constraint_start):
                    valid = False
                    break

            # Check if we can fly to this city
            if prev_city is not None:
                if city not in direct_flights[prev_city]:
                    valid = False
                    break
                itinerary.append({
                    'flying': f'Day {current_day-1}-{current_day-1}',
                    'from': prev_city,
                    'to': city
                })

            # Add stay
            itinerary.append({
                'day_range': f'Day {current_day}-{end_day}',
                'place': city
            })

            prev_city = city
            current_day = end_day + 1

            # Check if we exceeded total days
            if current_day - 1 > total_days:
                valid = False
                break

        # Check if all days are used
        if valid and (current_day - 1) == total_days:
            valid_itineraries.append(itinerary)

    # Select the first valid itinerary (all should be equivalent in days)
    if valid_itineraries:
        return valid_itineraries[0]
    else:
        return None

def main():
    itinerary = find_itinerary()
    if itinerary:
        print(json.dumps(itinerary, indent=2))
    else:
        print(json.dumps({"error": "No valid itinerary found"}, indent=2))

if __name__ == "__main__":
    main()