import json

def main():
    # Define cities with their durations and fixed start days
    cities = {
        'Reykjavik': {'duration': 4, 'fixed_start': 1},
        'Stuttgart': {'duration': 4, 'fixed_start': 4},
        'Valencia': {'duration': 5, 'fixed_start': None},
        'Seville': {'duration': 3, 'fixed_start': None},
        'Munich': {'duration': 3, 'fixed_start': 13},
        'Geneva': {'duration': 5, 'fixed_start': None},
        'Istanbul': {'duration': 4, 'fixed_start': 19},
        'Vilnius': {'duration': 4, 'fixed_start': None},
    }

    # Define the order of cities based on constraints and direct flights
    order = ['Reykjavik', 'Stuttgart', 'Valencia', 'Seville', 'Munich', 'Geneva', 'Istanbul', 'Vilnius']

    # Define direct flight connections
    direct_flights = {
        ('Geneva', 'Istanbul'),
        ('Istanbul', 'Geneva'),
        ('Reykjavik', 'Munich'),
        ('Munich', 'Reykjavik'),
        ('Stuttgart', 'Valencia'),
        ('Valencia', 'Stuttgart'),
        ('Reykjavik', 'Stuttgart'),
        ('Stuttgart', 'Reykjavik'),
        ('Stuttgart', 'Istanbul'),
        ('Istanbul', 'Stuttgart'),
        ('Munich', 'Geneva'),
        ('Geneva', 'Munich'),
        ('Istanbul', 'Vilnius'),
        ('Vilnius', 'Istanbul'),
        ('Valencia', 'Seville'),
        ('Seville', 'Valencia'),
        ('Valencia', 'Istanbul'),
        ('Istanbul', 'Valencia'),
        ('Vilnius', 'Munich'),
        ('Munich', 'Vilnius'),
        ('Seville', 'Munich'),
        ('Munich', 'Seville'),
        ('Munich', 'Istanbul'),
        ('Istanbul', 'Munich'),
        ('Valencia', 'Geneva'),
        ('Geneva', 'Valencia'),
        ('Valencia', 'Munich'),
        ('Munich', 'Valencia'),
    }

    # Check that each consecutive pair in order has a direct flight
    for i in range(len(order) - 1):
        current_city = order[i]
        next_city = order[i + 1]
        if (current_city, next_city) not in direct_flights:
            raise ValueError(f"No direct flight from {current_city} to {next_city}")

    # Generate the itinerary
    itinerary = []
    current_day = 1

    for city in order:
        city_data = cities[city]
        if city_data['fixed_start'] is not None:
            current_day = city_data['fixed_start']
        start_day = current_day
        end_day = start_day + city_data['duration'] - 1
        itinerary.append({
            'day_range': f"Day {start_day}-{end_day}",
            'place': city
        })
        current_day = end_day  # next city starts on this day

    # Output as JSON
    result = {'itinerary': itinerary}
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()