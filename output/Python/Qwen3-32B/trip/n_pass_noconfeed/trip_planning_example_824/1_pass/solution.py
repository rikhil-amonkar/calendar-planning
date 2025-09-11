import json

def main():
    # Define direct flights as adjacency list
    direct_flights = {
        'Berlin': ['Lisbon', 'Split', 'Riga', 'Tallinn'],
        'Lisbon': ['Berlin', 'Bucharest', 'Riga', 'Lyon'],
        'Bucharest': ['Lisbon', 'Riga', 'Lyon'],
        'Riga': ['Bucharest', 'Berlin', 'Lyon', 'Lisbon', 'Tallinn'],
        'Split': ['Berlin', 'Lyon'],
        'Lyon': ['Split', 'Lisbon', 'Bucharest'],
        'Tallinn': ['Riga'],
    }

    # Define cities with their required durations and time constraints
    cities = {
        'Berlin': {'days': 5, 'start': 1, 'end': 5},
        'Split': {'days': 3},
        'Lyon': {'days': 5, 'start': 7, 'end': 11},
        'Bucharest': {'days': 3, 'start': 13, 'end': 15},
        'Riga': {'days': 5},
        'Lisbon': {'days': 3},
        'Tallinn': {'days': 4},
    }

    # Plan the itinerary
    itinerary = []
    current_day = 1

    # Add Berlin first
    berlin_days = cities['Berlin']['days']
    end_day = current_day + berlin_days - 1
    itinerary.append({"day_range": f"Day {current_day}-{end_day}", "place": "Berlin"})
    current_day = end_day

    # Next cities in order: Split, Lyon, Lisbon, Bucharest, Riga, Tallinn
    next_cities_order = ['Split', 'Lyon', 'Lisbon', 'Bucharest', 'Riga', 'Tallinn']
    previous_city = 'Berlin'

    for city in next_cities_order:
        # Check if transition is allowed
        if previous_city not in direct_flights or city not in direct_flights[previous_city]:
            raise ValueError(f"No direct flight from {previous_city} to {city}")

        # Get the required days for the city
        days = cities[city]['days']
        start_day = current_day
        end_day = start_day + days - 1

        # For cities with fixed start/end, adjust if needed
        if 'start' in cities[city]:
            start_day = cities[city]['start']
            end_day = start_day + days - 1
            # Check if this fits with current_day
            if start_day != current_day:
                raise ValueError(f"Current day {current_day} does not match required start day {start_day} for {city}")

        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
        current_day = end_day
        previous_city = city

    # Output the result as JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()