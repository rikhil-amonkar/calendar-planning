import itertools
import json

def main():
    cities = ['Porto', 'Geneva', 'Mykonos', 'Manchester', 'Hamburg', 'Naples', 'Frankfurt']
    durations = {
        'Porto': 2,
        'Geneva': 3,
        'Mykonos': 3,
        'Manchester': 4,
        'Hamburg': 2,     # ← Fixed from 5 to 2
        'Naples': 2,      # ← Fixed from 5 to 2
        'Frankfurt': 2
    }
    
    # Direct flights as a set of frozensets
    direct_flights = {
        frozenset(['Hamburg', 'Frankfurt']),
        frozenset(['Naples', 'Mykonos']),
        frozenset(['Hamburg', 'Porto']),
        frozenset(['Hamburg', 'Geneva']),
        frozenset(['Mykonos', 'Geneva']),
        frozenset(['Frankfurt', 'Geneva']),
        frozenset(['Frankfurt', 'Porto']),
        frozenset(['Geneva', 'Porto']),
        frozenset(['Geneva', 'Manchester']),
        frozenset(['Naples', 'Manchester']),
        frozenset(['Frankfurt', 'Manchester']),
        frozenset(['Naples', 'Geneva']),
        frozenset(['Porto', 'Manchester']),
        frozenset(['Hamburg', 'Manchester'])
    }
    
    # Find valid permutation
    for perm in itertools.permutations(cities):
        start_day = 1
        city_days = {}
        valid = True
        for i, city in enumerate(perm):
            end_day = start_day + durations[city] - 1
            city_days[city] = (start_day, end_day)
            start_day = end_day + 1
        
        # Check if the last city ends on day 18
        if city_days[perm[-1]][1] != 18:
            continue
        
        # Check fixed cities' start days
        if city_days.get('Frankfurt', (0, 0))[0] != 5:
            continue
        if city_days.get('Mykonos', (0, 0))[0] != 10:
            continue
        if city_days.get('Manchester', (0, 0))[0] != 15:
            continue
        
        # Check transitions
        for i in range(len(perm) - 1):
            current = perm[i]
            next_city = perm[i+1]
            if frozenset([current, next_city]) not in direct_flights:
                valid = False
                break
        
        if not valid:
            continue
        
        # Build itinerary
        itinerary = []
        for city in perm:
            start, end = city_days[city]
            day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city})
        
        print(json.dumps({"itinerary": itinerary}))
        return

if __name__ == "__main__":
    main()