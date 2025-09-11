import json

def main():
    # Define cities and their required durations
    cities = {
        'Berlin': 3,
        'Barcelona': 2,
        'Lyon': 2,
        'Nice': 5,
        'Athens': 5,
        'Vilnius': 4,
        'Stockholm': 5
    }
    
    # Define the order of cities based on constraints and flight connections
    order = ['Berlin', 'Barcelona', 'Lyon', 'Nice', 'Athens', 'Vilnius', 'Stockholm']
    
    # Define direct flight connections (as a set of tuples)
    direct_flights = {
        ('Lyon', 'Nice'), ('Stockholm', 'Athens'), ('Nice', 'Athens'),
        ('Berlin', 'Athens'), ('Berlin', 'Nice'), ('Berlin', 'Barcelona'),
        ('Berlin', 'Vilnius'), ('Barcelona', 'Nice'), ('Athens', 'Vilnius'),
        ('Berlin', 'Stockholm'), ('Nice', 'Stockholm'), ('Barcelona', 'Athens'),
        ('Barcelona', 'Stockholm'), ('Barcelona', 'Lyon')
    }
    
    # Verify that all transitions between cities in the order are valid
    for i in range(len(order) - 1):
        current, next_city = order[i], order[i + 1]
        if (current, next_city) not in direct_flights:
            raise ValueError(f"No direct flight from {current} to {next_city}")
    
    # Calculate day ranges for each city
    current_day = 1
    itinerary = []
    for city in order:
        duration = cities[city]
        end_day = current_day + duration - 1
        day_range = f"Day {current_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city})
        current_day = end_day
    
    # Output the itinerary as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()