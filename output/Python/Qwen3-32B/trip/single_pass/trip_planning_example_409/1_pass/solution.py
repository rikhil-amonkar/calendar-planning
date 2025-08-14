import itertools
import json

def main():
    # Define cities and their required durations
    cities = ['Zurich', 'Hamburg', 'Helsinki', 'Bucharest', 'Split']
    durations = {
        'Zurich': 3,
        'Hamburg': 2,
        'Helsinki': 2,
        'Bucharest': 2,
        'Split': 7
    }
    
    # Define direct flight connections (bidirectional)
    direct_flights = {
        'Zurich': ['Helsinki', 'Hamburg', 'Bucharest', 'Split'],
        'Hamburg': ['Zurich', 'Bucharest', 'Helsinki', 'Split'],
        'Helsinki': ['Zurich', 'Hamburg', 'Split'],
        'Bucharest': ['Zurich', 'Hamburg'],
        'Split': ['Zurich', 'Hamburg', 'Helsinki']
    }
    
    # Generate all permutations of cities
    for perm in itertools.permutations(cities):
        valid = True
        # Check if consecutive cities have direct flights
        for i in range(len(perm) - 1):
            current = perm[i]
            next_city = perm[i+1]
            if next_city not in direct_flights[current]:
                valid = False
                break
        if not valid:
            continue
        
        # Calculate day ranges for each city in the permutation
        day_ranges = []
        current_start_day = 1
        for city in perm:
            duration = durations[city]
            end_day = current_start_day + duration - 1
            day_ranges.append((current_start_day, end_day))
            current_start_day = end_day  # Transition day is counted for both
        
        # Check if total days is 12
        total_days = day_ranges[-1][1]
        if total_days != 12:
            continue
        
        # Check Zurich's days (must be 1-3)
        zurich_index = perm.index('Zurich')
        zurich_start, zurich_end = day_ranges[zurich_index]
        if zurich_start != 1 or zurich_end != 3:
            continue
        
        # Check Split's days (must be 4-10)
        split_index = perm.index('Split')
        split_start, split_end = day_ranges[split_index]
        if split_start != 4 or split_end != 10:
            continue
        
        # If all conditions are met, build the itinerary
        itinerary = []
        for i in range(len(perm)):
            city = perm[i]
            start, end = day_ranges[i]
            itinerary.append({
                'day_range': f"Day {start}-{end}",
                'place': city
            })
        
        # Output as JSON
        print(json.dumps({'itinerary': itinerary}, indent=2))
        return  # Stop after finding the first valid itinerary

if __name__ == "__main__":
    main()