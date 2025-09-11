import itertools
import json

def main():
    # Define the graph of direct flights (undirected)
    flights = {
        "Geneva": ["Munich", "Valencia"],
        "Munich": ["Geneva", "Valencia", "Bucharest"],
        "Valencia": ["Geneva", "Munich", "Bucharest", "Stuttgart"],
        "Bucharest": ["Munich", "Valencia"],
        "Stuttgart": ["Valencia"]
    }
    
    # Required days for each city
    days_required = {
        "Geneva": 4,
        "Munich": 7,
        "Valencia": 6,
        "Bucharest": 2,
        "Stuttgart": 2
    }
    
    cities = list(days_required.keys())
    valid_permutations = []
    
    # Generate all permutations of the cities
    for perm in itertools.permutations(cities):
        # Check if consecutive cities have direct flights
        valid = True
        for i in range(len(perm) - 1):
            if perm[i+1] not in flights[perm[i]]:
                valid = False
                break
        if valid:
            valid_permutations.append(perm)
    
    # If no valid permutation found, return empty itinerary
    if not valid_permutations:
        print('{"itinerary": []}')
        return
        
    # For each valid permutation, compute start and end days and check constraints
    for perm in valid_permutations:
        start_days = {}
        end_days = {}
        current_start = 1
        for city in perm:
            d = days_required[city]
            end = current_start + d - 1
            start_days[city] = current_start
            end_days[city] = end
            current_start = end  # Next city starts on the same day (shared day)
        
        # Check constraints for Geneva and Munich
        geneva_start = start_days.get("Geneva", float('inf'))
        geneva_end = end_days.get("Geneva", -1)
        munich_start = start_days.get("Munich", float('inf'))
        munich_end = end_days.get("Munich", -1)
        
        # Geneva must have at least one day between 1 and 4
        if not (geneva_start <= 4 and geneva_end >= 1):
            continue
        # Munich must have at least one day between 4 and 10
        if not (munich_start <= 10 and munich_end >= 4):
            continue
            
        # Found valid itinerary
        itinerary = []
        for city in perm:
            start = start_days[city]
            end = end_days[city]
            day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city})
        
        print(json.dumps({"itinerary": itinerary}))
        return
        
    # If no permutation satisfies constraints
    print('{"itinerary": []}')

if __name__ == "__main__":
    main()