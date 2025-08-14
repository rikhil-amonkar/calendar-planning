import itertools
import json

def main():
    # Define input parameters
    cities = ['Krakow', 'Paris', 'Seville']
    days_required = {
        'Krakow': 5,
        'Paris': 2,
        'Seville': 6
    }
    direct_flights = {('Krakow', 'Paris'), ('Paris', 'Krakow'), ('Paris', 'Seville'), ('Seville', 'Paris')}

    # Generate all valid sequences of cities with direct flights between consecutive cities
    valid_sequences = []
    for seq in itertools.permutations(cities):
        valid = True
        for i in range(len(seq) - 1):
            if (seq[i], seq[i + 1]) not in direct_flights:
                valid = False
                break
        if valid:
            valid_sequences.append(seq)

    # Find the sequence that starts with Krakow (to satisfy the workshop constraint)
    cities_in_order = None
    for seq in valid_sequences:
        if seq[0] == 'Krakow':
            cities_in_order = seq
            break

    if cities_in_order is None:
        # No valid sequence found
        raise ValueError("No valid itinerary found")

    # Compute the day ranges
    itinerary = []
    prev_end = 0
    for city in cities_in_order:
        start_day = 1 if prev_end == 0 else prev_end
        duration = days_required[city]
        end_day = start_day + duration - 1
        day_range = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city})
        prev_end = end_day

    # Output as JSON
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()