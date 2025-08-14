import itertools
import json

def main():
    cities = ['Barcelona', 'Oslo', 'Venice', 'Split', 'Stuttgart', 'Brussels', 'Copenhagen']
    durations = {
        'Barcelona': 3,
        'Oslo': 2,
        'Venice': 4,
        'Split': 4,
        'Stuttgart': 3,
        'Brussels': 3,
        'Copenhagen': 3
    }
    
    # Define direct flights as a set of bidirectional pairs
    direct_flights = {
        ('Venice', 'Stuttgart'), ('Stuttgart', 'Venice'),
        ('Oslo', 'Brussels'), ('Brussels', 'Oslo'),
        ('Split', 'Copenhagen'), ('Copenhagen', 'Split'),
        ('Barcelona', 'Copenhagen'), ('Copenhagen', 'Barcelona'),
        ('Barcelona', 'Venice'), ('Venice', 'Barcelona'),
        ('Brussels', 'Venice'), ('Venice', 'Brussels'),
        ('Barcelona', 'Stuttgart'), ('Stuttgart', 'Barcelona'),
        ('Copenhagen', 'Brussels'), ('Brussels', 'Copenhagen'),
        ('Oslo', 'Split'), ('Split', 'Oslo'),
        ('Oslo', 'Venice'), ('Venice', 'Oslo'),
        ('Barcelona', 'Split'), ('Split', 'Barcelona'),
        ('Oslo', 'Copenhagen'), ('Copenhagen', 'Oslo'),
        ('Barcelona', 'Oslo'), ('Oslo', 'Barcelona'),
        ('Copenhagen', 'Stuttgart'), ('Stuttgart', 'Copenhagen'),
        ('Split', 'Stuttgart'), ('Stuttgart', 'Split'),
        ('Copenhagen', 'Venice'), ('Venice', 'Copenhagen'),
        ('Barcelona', 'Brussels'), ('Brussels', 'Barcelona'),
    }
    
    # Generate all permutations
    for perm in itertools.permutations(cities):
        # Calculate start and end days for each city in the permutation
        start_days = {}
        end_days = {}
        current_day = 1
        valid = True
        
        # Check Barcelona is first and meets the duration
        if perm[0] != 'Barcelona':
            continue
        start_days[perm[0]] = current_day
        end_days[perm[0]] = current_day + durations[perm[0]] - 1
        if end_days[perm[0]] != 3:
            continue  # Barcelona must end on day 3
        current_day = end_days[perm[0]]  # Now current_day is 3
        
        # Check other cities
        for i in range(1, len(perm)):
            city = perm[i]
            start_days[city] = current_day
            end_days[city] = current_day + durations[city] - 1
            current_day = end_days[city]
        
        # Check total days is 16
        if current_day != 16:
            continue
        
        # Check Oslo's days
        if 'Oslo' not in perm:
            continue
        oslo_index = perm.index('Oslo')
        oslo_start = start_days['Oslo']
        oslo_end = end_days['Oslo']
        if oslo_start != 3 or oslo_end != 4:
            continue
        
        # Check Brussels' days
        brussels_index = perm.index('Brussels')
        brussels_start = start_days['Brussels']
        brussels_end = end_days['Brussels']
        # Check if any of days 9-11 is in [brussels_start, brussels_end]
        if not (brussels_start <= 9 <= brussels_end or
                brussels_start <= 10 <= brussels_end or
                brussels_start <= 11 <= brussels_end):
            continue
        
        # Check transitions between cities
        for i in range(len(perm) - 1):
            city_a = perm[i]
            city_b = perm[i+1]
            if (city_a, city_b) not in direct_flights:
                valid = False
                break
        if not valid:
            continue
        
        # If we reach here, permutation is valid
        # Construct the itinerary
        itinerary = []
        current_day = 1
        for city in perm:
            start = current_day
            end = current_day + durations[city] - 1
            day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city})
            current_day = end
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
        return
    
    # If no valid itinerary found
    print(json.dumps({"error": "No valid itinerary found"}))

if __name__ == "__main__":
    main()