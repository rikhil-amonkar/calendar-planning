import itertools
import json

def main():
    cities = ['Valencia', 'Athens', 'Naples', 'Zurich']
    durations = {
        'Valencia': 6,
        'Athens': 6,
        'Naples': 5,
        'Zurich': 6
    }
    
    # Direct flight connections (bidirectional)
    direct_flights = {
        ('Valencia', 'Naples'),
        ('Naples', 'Valencia'),
        ('Valencia', 'Athens'),
        ('Athens', 'Valencia'),
        ('Athens', 'Naples'),
        ('Naples', 'Athens'),
        ('Zurich', 'Naples'),
        ('Naples', 'Zurich'),
        ('Athens', 'Zurich'),
        ('Zurich', 'Athens'),
        ('Zurich', 'Valencia'),
        ('Valencia', 'Zurich'),
    }
    
    # Generate all permutations of the cities
    for perm in itertools.permutations(cities):
        valid = True
        # Check if consecutive cities have direct flights
        for i in range(len(perm)-1):
            city1 = perm[i]
            city2 = perm[i+1]
            if (city1, city2) not in direct_flights:
                valid = False
                break
        if not valid:
            continue
        
        # Compute start and end days for each city in the permutation
        start_days = []
        end_days = []
        current_start = 1
        for city in perm:
            dur = durations[city]
            end = current_start + dur - 1
            start_days.append(current_start)
            end_days.append(end)
            current_start = end  # next city starts on the end day of previous
        
        # Now check constraints
        # Find index of Naples and Athens
        n_index = perm.index('Naples') if 'Naples' in perm else -1
        a_index = perm.index('Athens') if 'Athens' in perm else -1
        
        # Check if Naples is the last city and starts on day 16
        if n_index != 3:  # since indexes are 0-based, 3 is fourth position
            continue
        # Check Naples start day is 16
        n_start = start_days[n_index]
        if n_start != 16:
            continue
        
        # Check Athens' days include day 1-6
        # The stay in Athens must include at least day 1-6. Since the wedding is between day 1-6.
        # So, the end day of Athens must be >=6 and start day <=6
        a_start = start_days[a_index]
        a_end = end_days[a_index]
        if not (a_start <= 6 and a_end >= 6):
            continue
        
        # If all constraints are met, build the itinerary
        itinerary = []
        for i in range(len(perm)):
            day_range = f"Day {start_days[i]}-{end_days[i]}"
            itinerary.append({"day_range": day_range, "place": perm[i]})
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}, indent=2))
        return
    
    # If no valid itinerary found
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()