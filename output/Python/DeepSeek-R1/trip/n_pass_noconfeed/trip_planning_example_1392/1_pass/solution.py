import itertools
import json

def main():
    # Define the durations for the non-fixed cities
    durations_dict = {
        'Naples': 3,
        'Valencia': 5,
        'Stuttgart': 2,
        'Split': 5,
        'Amsterdam': 4,
        'Nice': 2,
        'Porto': 4
    }
    
    # Define the direct flight connections as a set of tuples
    direct_flights_input = [
        "Venice and Nice", "Naples and Amsterdam", "Barcelona and Nice", 
        "Amsterdam and Nice", "Stuttgart and Valencia", "Stuttgart and Porto", 
        "Split and Stuttgart", "Split and Naples", "Valencia and Amsterdam", 
        "Barcelona and Porto", "Valencia and Naples", "Venice and Amsterdam", 
        "Barcelona and Naples", "Barcelona and Valencia", "Split and Amsterdam", 
        "Barcelona and Venice", "Stuttgart and Amsterdam", "Naples and Nice", 
        "Venice and Stuttgart", "Split and Barcelona", "Porto and Nice", 
        "Barcelona and Stuttgart", "Venice and Naples", "Porto and Amsterdam", 
        "Porto and Valencia", "Stuttgart and Naples", "Barcelona and Amsterdam"
    ]
    
    flight_set = set()
    for pair in direct_flights_input:
        cities = pair.split(" and ")
        flight_set.add((cities[0], cities[1]))
        flight_set.add((cities[1], cities[0]))
    
    # Cities for the non-fixed parts
    all_cities = ['Naples', 'Valencia', 'Stuttgart', 'Split', 'Amsterdam', 'Nice', 'Porto']
    
    # We'll try j=1 and j=2 for the before part (number of cities before Barcelona)
    found_solution = False
    result_itinerary = None
    
    # j=1: one city before Barcelona
    for before_city in ['Valencia', 'Split']:
        before_part = [before_city]
        # Check flight from before_city to Barcelona
        if (before_city, 'Barcelona') not in flight_set and ('Barcelona', before_city) not in flight_set:
            continue
        
        boundaries_before = [1]
        boundaries_before.append(boundaries_before[0] + durations_dict[before_city] - 1)
        if boundaries_before[-1] != 5:
            continue
        
        after_cities = [c for c in all_cities if c != before_city]
        for perm in itertools.permutations(after_cities):
            boundaries_after = [10]
            for c in perm:
                boundaries_after.append(boundaries_after[-1] + durations_dict[c] - 1)
            if boundaries_after[-1] != 24:
                continue
            
            if not (('Venice', perm[0]) in flight_set or (perm[0], 'Venice') in flight_set):
                continue
            
            valid_flight = True
            for i in range(len(perm)-1):
                if not ((perm[i], perm[i+1]) in flight_set or (perm[i+1], perm[i]) in flight_set):
                    valid_flight = False
                    break
            if not valid_flight:
                continue
            
            naples_ok = False
            nice_ok = False
            for i, city in enumerate(perm):
                start = boundaries_after[i]
                if city == 'Naples':
                    if start >= 16 and start <= 20:
                        naples_ok = True
                    else:
                        naples_ok = False
                        break
                if city == 'Nice':
                    if start == 22 or start == 23:
                        nice_ok = True
                    else:
                        nice_ok = False
                        break
            if not naples_ok or not nice_ok:
                continue
            
            itinerary = []
            itinerary.append({"day_range": f"Day 1-{boundaries_before[1]}", "place": before_city})
            itinerary.append({"day_range": "Day 5-6", "place": "Barcelona"})
            itinerary.append({"day_range": "Day 6-10", "place": "Venice"})
            for i, city in enumerate(perm):
                start = boundaries_after[i]
                end = boundaries_after[i+1]
                itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
            
            found_solution = True
            result_itinerary = itinerary
            break
        if found_solution:
            break
    
    if found_solution:
        print(json.dumps({"itinerary": result_itinerary}))
        return
    
    # j=2: two cities before Barcelona
    before_candidates = [['Stuttgart', 'Amsterdam'], ['Stuttgart', 'Porto']]
    for candidate in before_candidates:
        for perm_before in itertools.permutations(candidate):
            total_duration = durations_dict[perm_before[0]] + durations_dict[perm_before[1]]
            if total_duration != 6:
                continue
            boundaries_before = [1]
            boundaries_before.append(boundaries_before[0] + durations_dict[perm_before[0]] - 1)
            boundaries_before.append(boundaries_before[1] + durations_dict[perm_before[1]] - 1)
            if boundaries_before[-1] != 5:
                continue
            valid_flight_before = True
            for i in range(len(perm_before)-1):
                if not ((perm_before[i], perm_before[i+1]) in flight_set or (perm_before[i+1], perm_before[i]) in flight_set):
                    valid_flight_before = False
                    break
            if not valid_flight_before:
                continue
            if not ((perm_before[-1], 'Barcelona') in flight_set or ('Barcelona', perm_before[-1]) in flight_set):
                continue
            
            after_cities = [c for c in all_cities if c not in perm_before]
            for perm_after in itertools.permutations(after_cities):
                boundaries_after = [10]
                for c in perm_after:
                    boundaries_after.append(boundaries_after[-1] + durations_dict[c] - 1)
                if boundaries_after[-1] != 24:
                    continue
                if not (('Venice', perm_after[0]) in flight_set or (perm_after[0], 'Venice') in flight_set):
                    continue
                valid_flight_after = True
                for i in range(len(perm_after)-1):
                    if not ((perm_after[i], perm_after[i+1]) in flight_set or (perm_after[i+1], perm_after[i]) in flight_set):
                        valid_flight_after = False
                        break
                if not valid_flight_after:
                    continue
                naples_ok = False
                nice_ok = False
                for i, city in enumerate(perm_after):
                    start = boundaries_after[i]
                    if city == 'Naples':
                        if start >= 16 and start <= 20:
                            naples_ok = True
                        else:
                            naples_ok = False
                            break
                    if city == 'Nice':
                        if start == 22 or start == 23:
                            nice_ok = True
                        else:
                            nice_ok = False
                            break
                if not naples_ok or not nice_ok:
                    continue
                
                itinerary = []
                start_day = 1
                for i, city in enumerate(perm_before):
                    end_day = start_day + durations_dict[city] - 1
                    itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
                    start_day = end_day
                itinerary.append({"day_range": "Day 5-6", "place": "Barcelona"})
                itinerary.append({"day_range": "Day 6-10", "place": "Venice"})
                for i, city in enumerate(perm_after):
                    start = boundaries_after[i]
                    end = boundaries_after[i+1]
                    itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
                
                found_solution = True
                result_itinerary = itinerary
                break
            if found_solution:
                break
        if found_solution:
            break
    
    if found_solution:
        print(json.dumps({"itinerary": result_itinerary}))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()