import json
from itertools import permutations

def main():
    # Define the required data
    durations = {
        'Vienna': 2,
        'Nice': 2,
        'Stockholm': 5,
        'Split': 3
    }
    allowed_transitions = {
        'Vienna': ['Nice', 'Stockholm', 'Split'],
        'Nice': ['Vienna', 'Stockholm'],
        'Stockholm': ['Vienna', 'Nice', 'Split'],
        'Split': ['Vienna', 'Stockholm']
    }
    required_cities = ['Vienna', 'Nice', 'Stockholm', 'Split']
    
    # Generate all permutations of the remaining cities after Vienna
    remaining_cities = ['Nice', 'Stockholm', 'Split']
    for perm in permutations(remaining_cities):
        order = ['Vienna'] + list(perm)
        # Check transitions between consecutive cities
        valid = True
        for i in range(len(order)-1):
            current = order[i]
            next_city = order[i+1]
            if next_city not in allowed_transitions[current]:
                valid = False
                break
        if not valid:
            continue
        
        # Calculate start and end days
        start_days = {}
        end_days = {}
        start_days[order[0]] = 1
        end_days[order[0]] = 1 + durations[order[0]] - 1
        
        for i in range(1, len(order)):
            prev_city = order[i-1]
            start_days[order[i]] = end_days[prev_city]
            end_days[order[i]] = start_days[order[i]] + durations[order[i]] - 1
        
        # Check Split's days
        split_start = start_days.get('Split', None)
        split_end = end_days.get('Split', None)
        if split_start is not None and split_end == 9 and split_start == 7:
            # Check all cities are covered
            if set(order) == set(required_cities):
                # Build the itinerary
                itinerary = []
                for city in order:
                    start = start_days[city]
                    end = end_days[city]
                    day_range = f"Day {start}-{end}"
                    itinerary.append({"day_range": day_range, "place": city})
                # Output as JSON
                print(json.dumps({"itinerary": itinerary}, indent=2))
                return
    
    # If no valid itinerary found
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()