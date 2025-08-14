import itertools
import json

def main():
    cities = {
        'Helsinki': 4,
        'Valencia': 5,
        'Dubrovnik': 4,
        'Porto': 3,
        'Prague': 3,
        'Reykjavik': 4
    }
    
    allowed_flights = {
        ('Helsinki', 'Prague'),
        ('Prague', 'Helsinki'),
        ('Prague', 'Valencia'),
        ('Valencia', 'Prague'),
        ('Valencia', 'Porto'),
        ('Porto', 'Valencia'),
        ('Helsinki', 'Reykjavik'),
        ('Reykjavik', 'Helsinki'),
        ('Dubrovnik', 'Helsinki'),
        ('Helsinki', 'Dubrovnik'),
        ('Reykjavik', 'Prague'),
        ('Prague', 'Reykjavik'),
    }
    
    city_list = list(cities.keys())
    
    for perm in itertools.permutations(city_list):
        # Check if the last three cities are Prague, Valencia, Porto in positions 3,4,5 (0-based)
        if perm[3] != 'Prague' or perm[4] != 'Valencia' or perm[5] != 'Porto':
            continue
        
        # Check if all consecutive transitions are allowed
        valid = True
        for i in range(5):
            if (perm[i], perm[i+1]) not in allowed_flights:
                valid = False
                break
        if not valid:
            continue
        
        # Found a valid permutation
        itinerary = []
        current_start = 1
        for city in perm:
            duration = cities[city]
            end_day = current_start + duration - 1
            day_range = f"Day {current_start}-{end_day}"
            itinerary.append({"day_range": day_range, "place": city})
            current_start = end_day
        
        # Output the JSON
        print(json.dumps({"itinerary": itinerary}))
        return
    
    # If no itinerary found
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()