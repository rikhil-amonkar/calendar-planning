import itertools
import json

def main():
    cities = {
        'Vienna': 4,
        'Lyon': 3,
        'Edinburgh': 4,
        'Reykjavik': 5,
        'Stuttgart': 5,
        'Manchester': 2,
        'Split': 5,
        'Prague': 4
    }
    
    fixed_order = ['Stuttgart', 'Edinburgh', 'Prague']
    fixed_days = sum(cities[city] for city in fixed_order)  # 13 days
    remaining_days = 25 - fixed_days  # 12 days
    remaining_cities = [city for city in cities if city not in fixed_order]
    
    graph = {
        'Lyon': ['Vienna', 'Split'],
        'Reykjavik': ['Vienna'],
        'Manchester': ['Vienna', 'Split'],
        'Split': ['Lyon', 'Manchester', 'Vienna'],
        'Vienna': ['Lyon', 'Reykjavik', 'Manchester', 'Split']
    }
    allowed_after_prague = ['Vienna', 'Reykjavik', 'Manchester']
    
    found = False
    result_perm = None
    # Only consider the full set of remaining cities
    subset = tuple(remaining_cities)
    if sum(cities[city] for city in subset) == remaining_days:
        # Generate permutations of the full set
        for perm in itertools.permutations(subset):
            # First city after Prague must be in allowed list
            if perm[0] not in allowed_after_prague:
                continue
            # Check connections between consecutive cities
            valid_chain = True
            for i in range(len(perm)-1):
                if perm[i+1] not in graph[perm[i]]:
                    valid_chain = False
                    break
            if not valid_chain:
                continue
            # Check Split position in entire itinerary
            if 'Split' in perm:
                idx = perm.index('Split')
                n = len(perm)
                # Ensure Split isn't last or second last in remaining part
                if idx == n-1 or idx == n-2:
                    continue
            # Valid permutation found
            found = True
            result_perm = perm
            break
            
    if not found:
        itinerary = []
    else:
        order = fixed_order + list(result_perm)
        start_day = 1
        blocks = []
        for city in order:
            duration = cities[city]
            end_day = start_day + duration - 1
            blocks.append((city, start_day, end_day))
            start_day = end_day + 1
        
        itinerary = []
        for city, start, end in blocks:
            if start == end:
                day_range_str = f"Day {start}"
            else:
                day_range_str = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range_str, "place": city})
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == '__main__':
    main()