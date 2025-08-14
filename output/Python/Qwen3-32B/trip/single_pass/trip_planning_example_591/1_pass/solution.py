import itertools
import json

def main():
    cities = ['Stuttgart', 'Bucharest', 'Geneva', 'Valencia', 'Munich']
    durations = {
        'Stuttgart': 2,
        'Bucharest': 2,
        'Geneva': 4,
        'Valencia': 6,
        'Munich': 7
    }
    flights = {
        'Stuttgart': ['Valencia'],
        'Valencia': ['Stuttgart', 'Munich', 'Bucharest', 'Geneva'],
        'Munich': ['Geneva', 'Valencia', 'Bucharest'],
        'Bucharest': ['Valencia', 'Munich'],
        'Geneva': ['Munich', 'Valencia']
    }

    # Generate all valid sequences
    valid_sequences = []
    for perm in itertools.permutations(cities):
        valid = True
        for i in range(len(perm) - 1):
            current = perm[i]
            next_city = perm[i + 1]
            if next_city not in flights[current]:
                valid = False
                break
        if valid:
            valid_sequences.append(perm)

    # Check each valid sequence for constraints
    for seq in valid_sequences:
        start_days = []
        end_days = []
        for i, city in enumerate(seq):
            if i == 0:
                start = 1
            else:
                start = end_days[-1]
            end = start + durations[city] - 1
            start_days.append(start)
            end_days.append(end)
        
        # Check Geneva and Munich constraints
        try:
            geneva_idx = seq.index('Geneva')
            geneva_start = start_days[geneva_idx]
        except ValueError:
            continue  # Geneva not in sequence (shouldn't happen)
        
        try:
            munich_idx = seq.index('Munich')
            munich_start = start_days[munich_idx]
        except ValueError:
            continue  # Munich not in sequence (shouldn't happen)
        
        if 1 <= geneva_start <= 4 and 4 <= munich_start <= 10:
            # Construct itinerary
            itinerary = []
            for i in range(len(seq)):
                day_range = f"Day {start_days[i]}-{end_days[i]}"
                city = seq[i]
                itinerary.append({"day_range": day_range, "place": city})
            print(json.dumps({"itinerary": itinerary}))
            return

    # If no valid itinerary found
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()