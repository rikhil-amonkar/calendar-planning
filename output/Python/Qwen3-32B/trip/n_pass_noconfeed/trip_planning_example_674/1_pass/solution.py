import itertools
import json

def main():
    cities = ['Helsinki', 'Warsaw', 'Madrid', 'Split', 'Reykjavik', 'Budapest']
    durations = {
        'Helsinki': 2,
        'Warsaw': 3,
        'Madrid': 4,
        'Split': 4,
        'Reykjavik': 2,
        'Budapest': 4
    }
    
    # Direct flights (bidirectional)
    direct_flights = {
        frozenset({'Helsinki', 'Reykjavik'}),
        frozenset({'Budapest', 'Warsaw'}),
        frozenset({'Madrid', 'Split'}),
        frozenset({'Helsinki', 'Split'}),
        frozenset({'Helsinki', 'Madrid'}),
        frozenset({'Helsinki', 'Budapest'}),
        frozenset({'Reykjavik', 'Warsaw'}),
        frozenset({'Helsinki', 'Warsaw'}),
        frozenset({'Madrid', 'Budapest'}),
        frozenset({'Budapest', 'Reykjavik'}),
        frozenset({'Madrid', 'Warsaw'}),
        frozenset({'Warsaw', 'Split'}),
        frozenset({'Reykjavik', 'Madrid'}),
    }
    
    # Remaining cities after Helsinki
    remaining_cities = ['Warsaw', 'Madrid', 'Split', 'Reykjavik', 'Budapest']
    
    for perm in itertools.permutations(remaining_cities):
        order = ['Helsinki'] + list(perm)
        # Compute start and end days for each city in the order
        start_days = [1]
        end_days = [start_days[0] + durations[order[0]] - 1]
        valid = True
        for i in range(1, len(order)):
            prev_end = end_days[-1]
            start_days.append(prev_end)
            current_duration = durations[order[i]]
            end_days.append(start_days[i] + current_duration - 1)
        
        # Check if Reykjavik's start day is 8 and Warsaw's is 9
        reykjavik_idx = order.index('Reykjavik') if 'Reykjavik' in order else -1
        warsaw_idx = order.index('Warsaw') if 'Warsaw' in order else -1
        
        if reykjavik_idx == -1 or warsaw_idx == -1:
            continue
        
        reyk_start = start_days[reykjavik_idx]
        war_start = start_days[warsaw_idx]
        
        if reyk_start != 8 or war_start != 9:
            continue
        
        # Check flight transitions
        for i in range(len(order) - 1):
            current = order[i]
            next_city = order[i+1]
            if frozenset({current, next_city}) not in direct_flights:
                valid = False
                break
        
        if valid:
            # Generate the itinerary
            itinerary = []
            for i in range(len(order)):
                start = start_days[i]
                end = end_days[i]
                day_range = f"Day {start}-{end}"
                itinerary.append({"day_range": day_range, "place": order[i]})
            print(json.dumps({"itinerary": itinerary}))
            return
    
    # If no valid itinerary found
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()