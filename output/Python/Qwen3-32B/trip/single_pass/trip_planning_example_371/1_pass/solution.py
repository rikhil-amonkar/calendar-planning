import itertools
import json

def main():
    # Define the cities and their required durations
    durations = {
        'Vienna': 2,
        'Nice': 2,
        'Stockholm': 5,
        'Split': 3
    }
    cities = list(durations.keys())
    
    # Define allowed direct flights (both directions)
    allowed_pairs = [
        ('Vienna', 'Nice'),
        ('Vienna', 'Stockholm'),
        ('Vienna', 'Split'),
        ('Stockholm', 'Split'),
        ('Nice', 'Stockholm')
    ]
    allowed_transitions = set()
    for a, b in allowed_pairs:
        allowed_transitions.add((a, b))
        allowed_transitions.add((b, a))
    
    # Generate all permutations of the cities
    for perm in itertools.permutations(cities):
        # Check if Vienna is first and Split is last
        if perm[0] != 'Vienna' or perm[-1] != 'Split':
            continue
        
        # Check if transitions between consecutive cities are allowed
        valid_transitions = True
        for i in range(len(perm) - 1):
            if (perm[i], perm[i+1]) not in allowed_transitions:
                valid_transitions = False
                break
        if not valid_transitions:
            continue
        
        # Calculate start day of Split
        current_start = 1  # Start day of the first city (Vienna)
        for i in range(len(perm) - 1):  # Process all cities except the last one
            current_city = perm[i]
            duration = durations[current_city]
            current_end = current_start + duration - 1
            current_start = current_end  # Start day of next city
        
        # Check if Split starts on day 7
        if current_start == 7:
            # Build the itinerary
            itinerary = []
            current_day = 1
            for city in perm:
                duration = durations[city]
                end_day = current_day + duration - 1
                day_range = f"Day {current_day}-{end_day}"
                itinerary.append({"day_range": day_range, "place": city})
                current_day = end_day  # Move to next start day
            
            # Output as JSON
            print(json.dumps({"itinerary": itinerary}, indent=2))
            return

if __name__ == "__main__":
    main()