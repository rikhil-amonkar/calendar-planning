import itertools
import json

def main():
    # Define the flight graph (bidirectional)
    graph = {
        'Oslo': ['Krakow', 'Paris', 'Madrid', 'Helsinki', 'Dubrovnik', 'Vilnius'],
        'Krakow': ['Oslo', 'Paris', 'Vilnius', 'Helsinki'],
        'Paris': ['Oslo', 'Madrid', 'Krakow', 'Helsinki', 'Vilnius'],
        'Madrid': ['Paris', 'Oslo', 'Dubrovnik', 'Helsinki', 'Mykonos'],
        'Helsinki': ['Vilnius', 'Oslo', 'Krakow', 'Dubrovnik', 'Paris', 'Madrid'],
        'Dubrovnik': ['Helsinki', 'Madrid', 'Oslo'],
        'Vilnius': ['Helsinki', 'Oslo', 'Krakow', 'Paris'],
        'Mykonos': ['Madrid']
    }
    
    # City requirements
    req = {
        'Krakow': 5,
        'Vilnius': 2,
        'Helsinki': 2,
        'Dubrovnik': 3,
        'Oslo': 2,
        'Paris': 2,
        'Madrid': 5,
        'Mykonos': 4
    }
    
    # Cities to permute (positions 0 to 5), and fixed cities for positions 6 and 7
    cities_permute = ['Krakow', 'Vilnius', 'Helsinki', 'Dubrovnik', 'Oslo', 'Paris']
    fixed = ['Madrid', 'Mykonos']
    itinerary_found = None

    for perm in itertools.permutations(cities_permute):
        # Check if Oslo is in the first two cities
        if 'Oslo' not in perm[0:2]:
            continue
            
        # Check flight connectivity within the permutation
        valid_flight = True
        for i in range(5):
            if perm[i+1] not in graph[perm[i]]:
                valid_flight = False
                break
        if not valid_flight:
            continue
            
        # Check flight from last city in permutation to Madrid
        if fixed[0] not in graph[perm[5]]:
            continue
            
        # Compute end_days from requirements
        try:
            end0 = req[perm[0]]
            end1 = req[perm[1]] + end0 - 1
            end2 = req[perm[2]] + end1 - 1
            end3 = req[perm[3]] + end2 - 1
            end4 = req[perm[4]] + end3 - 1
            d5 = 12 - end4
        except KeyError:
            continue
        
        # Check duration for the last city in permutation
        if d5 != req[perm[5]]:
            continue
            
        # Check if end_days are within [1,11] and in non-decreasing order
        if not (1 <= end0 <= end1 <= end2 <= end3 <= end4 <= 11):
            continue
            
        # Check Dubrovnik constraint if present
        if 'Dubrovnik' in perm:
            j = perm.index('Dubrovnik')
            if j == 0:
                start_j = 1
                end_j = end0
            elif j == 1:
                start_j = end0
                end_j = end1
            elif j == 2:
                start_j = end1
                end_j = end2
            elif j == 3:
                start_j = end2
                end_j = end3
            elif j == 4:
                start_j = end3
                end_j = end4
            else:  # j == 5
                start_j = end4
                end_j = 11
            if not (start_j <= 2 and end_j >= 4):
                continue
        
        # Build the itinerary
        itinerary = []
        # First city: from day 1 to end0
        itinerary.append({"day_range": f"Day 1-{end0}", "place": perm[0]})
        # Second city: from end0 to end1
        itinerary.append({"day_range": f"Day {end0}-{end1}", "place": perm[1]})
        # Third city: from end1 to end2
        itinerary.append({"day_range": f"Day {end1}-{end2}", "place": perm[2]})
        # Fourth city: from end2 to end3
        itinerary.append({"day_range": f"Day {end2}-{end3}", "place": perm[3]})
        # Fifth city: from end3 to end4
        itinerary.append({"day_range": f"Day {end3}-{end4}", "place": perm[4]})
        # Sixth city: from end4 to 11 (since end5=11)
        itinerary.append({"day_range": f"Day {end4}-11", "place": perm[5]})
        # Madrid: from day 11 to 15
        itinerary.append({"day_range": "Day 11-15", "place": "Madrid"})
        # Mykonos: from day 15 to 18
        itinerary.append({"day_range": "Day 15-18", "place": "Mykonos"})
        
        itinerary_found = itinerary
        break
    
    # Output the itinerary or an empty list if not found
    if itinerary_found is None:
        print(json.dumps({"itinerary": []}))
    else:
        print(json.dumps({"itinerary": itinerary_found}))

if __name__ == '__main__':
    main()