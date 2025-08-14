import itertools
import json

def main():
    # Define the cities and their required stay durations
    cities = ['Riga', 'Vilnius', 'Dublin']
    durations = {
        'Riga': 5,
        'Vilnius': 7,
        'Dublin': 2
    }
    
    # Define direct flight connections (bidirectional)
    flight_connections = {
        'Dublin': ['Riga'],
        'Riga': ['Dublin', 'Vilnius'],
        'Vilnius': ['Riga']
    }
    
    # Find all valid city sequences with allowed transitions
    valid_sequences = []
    for perm in itertools.permutations(cities):
        valid = True
        for i in range(len(perm) - 1):
            current_city = perm[i]
            next_city = perm[i+1]
            if next_city not in flight_connections[current_city]:
                valid = False
                break
        if valid:
            valid_sequences.append(perm)
    
    # Use the first valid sequence to build the itinerary
    city_sequence = valid_sequences[0]
    
    # Calculate day ranges for each city in the sequence
    itinerary = []
    current_day = 1
    for city in city_sequence:
        duration = durations[city]
        start_day = current_day
        end_day = start_day + duration - 1
        day_range = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city})
        current_day = end_day  # Next city starts on this day
    
    # Output as JSON
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()