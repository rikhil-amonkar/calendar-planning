import itertools
import json

def main():
    # Define parameters
    cities = ['Stuttgart', 'Seville', 'Manchester']
    durations = {
        'Stuttgart': 6,
        'Seville': 7,
        'Manchester': 4
    }
    flight_connections = {
        'Manchester': ['Stuttgart', 'Seville'],
        'Stuttgart': ['Manchester'],
        'Seville': ['Manchester']
    }
    
    # Find valid sequences
    valid_sequences = []
    for seq in itertools.permutations(cities):
        valid = True
        for i in range(len(seq) - 1):
            current = seq[i]
            next_city = seq[i + 1]
            if next_city not in flight_connections[current]:
                valid = False
                break
        if valid:
            valid_sequences.append(seq)
    
    # Filter sequences where Stuttgart is first (to meet friend constraint)
    candidate_sequences = [s for s in valid_sequences if s[0] == 'Stuttgart']
    if not candidate_sequences:
        # No valid sequence found
        return {"itinerary": []}
    sequence = candidate_sequences[0]  # Take the first valid one
    
    # Compute day ranges
    itinerary = []
    current_start = 1
    for city in sequence:
        dur = durations[city]
        end_day = current_start + dur - 1
        day_range = f"Day {current_start}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city})
        current_start = end_day  # Next city starts on this day (flight day)
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = main()
    print(json.dumps(result, indent=2))