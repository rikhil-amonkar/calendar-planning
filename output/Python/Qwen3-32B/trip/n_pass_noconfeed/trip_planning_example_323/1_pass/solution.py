import json

def main():
    # Define cities and their required durations
    durations = {
        'London': 7,
        'Split': 5,
        'Oslo': 2,
        'Porto': 5
    }
    
    # Define the order based on constraints and flight availability
    order = ['London', 'Split', 'Oslo', 'Porto']
    
    # Define direct flight connections between cities
    flights = {
        'London': {'Oslo', 'Split'},
        'Split': {'London', 'Oslo'},
        'Oslo': {'London', 'Split', 'Porto'},
        'Porto': {'Oslo'}
    }
    
    # Validate flight connections between consecutive cities in the order
    for i in range(len(order) - 1):
        current_city = order[i]
        next_city = order[i + 1]
        if next_city not in flights[current_city]:
            raise ValueError(f"No direct flight from {current_city} to {next_city}")
    
    # Calculate day ranges for each city in the itinerary
    itinerary = []
    current_day = 1
    for city in order:
        duration = durations[city]
        end_day = current_day + duration - 1
        day_range = f"Day {current_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city})
        current_day = end_day  # Next city starts on the same day as the flight
    
    # Output the result as a JSON-formatted dictionary
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()