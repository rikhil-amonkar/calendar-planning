import json
from itertools import permutations

def main():
    # Define the required days in each city
    durations = {
        'Stuttgart': 6,
        'Seville': 7,
        'Manchester': 4
    }
    
    # Define allowed direct flights between cities
    allowed_flights = {
        ('Stuttgart', 'Manchester'),
        ('Manchester', 'Stuttgart'),
        ('Manchester', 'Seville'),
        ('Seville', 'Manchester')
    }
    
    # Generate all valid sequences of cities
    valid_sequences = []
    cities = ['Stuttgart', 'Seville', 'Manchester']
    for seq in permutations(cities):
        if (seq[0], seq[1]) in allowed_flights and (seq[1], seq[2]) in allowed_flights:
            valid_sequences.append(seq)
    
    # Find the valid sequence that starts with Stuttgart (to meet friend constraint)
    for sequence in valid_sequences:
        if sequence[0] == 'Stuttgart':
            selected_sequence = sequence
            break
    else:
        # No valid sequence found
        return {"itinerary": []}
    
    # Calculate the itinerary day ranges
    itinerary = []
    current_start = 1
    for city in selected_sequence:
        city_duration = durations[city]
        end_day = current_start + city_duration - 1
        day_range = f"Day {current_start}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city})
        current_start = end_day
    
    # Output as JSON
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = main()
    print(json.dumps(result, indent=2))