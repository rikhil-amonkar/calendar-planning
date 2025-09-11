import itertools
import json
from collections import defaultdict

def main():
    cities = ['Reykjavik', 'Stockholm', 'Porto', 'Nice', 'Venice', 'Vienna', 'Split', 'Copenhagen']
    city_durations = {
        'Reykjavik': 2,
        'Stockholm': 2,
        'Porto': 5,
        'Nice': 3,
        'Venice': 4,
        'Vienna': 3,
        'Split': 3,
        'Copenhagen': 2
    }

    # Define direct flight connections
    connections = [
        ('Copenhagen', 'Vienna'),
        ('Nice', 'Stockholm'),
        ('Split', 'Copenhagen'),
        ('Nice', 'Reykjavik'),
        ('Nice', 'Porto'),
        ('Reykjavik', 'Vienna'),
        ('Stockholm', 'Copenhagen'),
        ('Nice', 'Venice'),
        ('Nice', 'Vienna'),
        ('Reykjavik', 'Copenhagen'),
        ('Nice', 'Copenhagen'),
        ('Stockholm', 'Vienna'),
        ('Venice', 'Vienna'),
        ('Copenhagen', 'Porto'),
        ('Reykjavik', 'Stockholm'),
        ('Stockholm', 'Split'),
        ('Split', 'Vienna'),
        ('Copenhagen', 'Venice'),
        ('Vienna', 'Porto'),
    ]
    direct_flights = defaultdict(set)
    for a, b in connections:
        direct_flights[a].add(b)
        direct_flights[b].add(a)

    # Generate all permutations and check constraints
    for perm in itertools.permutations(cities):
        # Check if all consecutive cities have direct flights
        valid_path = True
        for i in range(len(perm) - 1):
            current = perm[i]
            next_city = perm[i+1]
            if next_city not in direct_flights[current]:
                valid_path = False
                break
        if not valid_path:
            continue

        # Compute days for each city in the permutation
        days_info = []
        current_start = 1
        for city in perm:
            duration = city_durations[city]
            end_day = current_start + duration - 1
            days_info.append( (current_start, end_day) )
            current_start = end_day  # Next city starts at this end_day

        # Check constraints
        reykjavik_ok = False
        stockholm_ok = False
        porto_ok = False
        vienna_ok = False

        for i, city in enumerate(perm):
            s, e = days_info[i]
            if city == 'Reykjavik':
                if s == 3 and e == 4:
                    reykjavik_ok = True
            elif city == 'Stockholm':
                if s == 4 and e == 5:
                    stockholm_ok = True
            elif city == 'Porto':
                if s == 13 and e == 17:
                    porto_ok = True
            elif city == 'Vienna':
                # Check if Vienna's days overlap with 11-13
                if not (e < 11 or s > 13):
                    vienna_ok = True

        if reykjavik_ok and stockholm_ok and porto_ok and vienna_ok:
            # Found a valid itinerary
            itinerary = []
            for i, city in enumerate(perm):
                s, e = days_info[i]
                day_range = f"Day {s}-{e}"
                itinerary.append({"day_range": day_range, "place": city})
            # Output as JSON
            print(json.dumps({"itinerary": itinerary}, indent=2))
            return

    print("No valid itinerary found.")

if __name__ == "__main__":
    main()