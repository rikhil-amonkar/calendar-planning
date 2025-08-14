import itertools
import json

def main():
    cities = ['London', 'Split', 'Oslo', 'Porto']
    durations = {
        'London': 7,
        'Split': 5,
        'Oslo': 2,
        'Porto': 5
    }
    # Flight connections
    edges = {
        'London': {'Oslo', 'Split'},
        'Oslo': {'London', 'Split', 'Porto'},
        'Split': {'London', 'Oslo'},
        'Porto': {'Oslo'}
    }

    # Generate all possible permutations of the 4 cities
    for perm in itertools.permutations(cities):
        valid_sequence = True
        # Check if consecutive cities have direct flights
        for i in range(1, len(perm)):
            prev_city = perm[i-1]
            current_city = perm[i]
            if current_city not in edges[prev_city]:
                valid_sequence = False
                break
        if not valid_sequence:
            continue
        
        # Now compute the day ranges for this sequence
        itinerary = []
        current_start = 1
        for city in perm:
            dur = durations[city]
            end = current_start + dur - 1
            itinerary.append( (current_start, end, city) )
            current_start = end  # next starts on this day
        
        # Check if last end day is 16
        if itinerary[-1][1] != 16:
            continue
        
        # Check London's end day is 7 and starts on or after 1
        london_entry = None
        split_entry = None
        oslo_entry = None
        porto_entry = None
        for entry in itinerary:
            if entry[2] == 'London':
                london_entry = entry
            elif entry[2] == 'Split':
                split_entry = entry
            elif entry[2] == 'Oslo':
                oslo_entry = entry
            elif entry[2] == 'Porto':
                porto_entry = entry
        
        # Check constraints
        if (london_entry is not None and
            split_entry is not None and
            oslo_entry is not None and
            porto_entry is not None):
            
            # London must end on day 7
            if london_entry[1] != 7:
                continue
            # Split must start on 7 and end on 11
            if split_entry[0] != 7 or split_entry[1] != 11:
                continue
            # Oslo's duration is 2 days
            if (oslo_entry[1] - oslo_entry[0] + 1) != 2:
                continue
            # Porto's duration is 5 days
            if (porto_entry[1] - porto_entry[0] + 1) != 5:
                continue
            
            # If all checks passed, build the JSON
            json_itinerary = []
            for start, end, city in itinerary:
                day_range = f"Day {start}-{end}"
                json_itinerary.append({"day_range": day_range, "place": city})
            
            result = {"itinerary": json_itinerary}
            print(json.dumps(result, indent=2))
            return  # Assuming first valid one is the solution

    # If no valid itinerary found
    print(json.dumps({"error": "No valid itinerary found"}))

if __name__ == "__main__":
    main()