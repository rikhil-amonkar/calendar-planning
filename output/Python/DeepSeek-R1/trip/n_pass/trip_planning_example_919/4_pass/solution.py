import itertools
import json

def main():
    # Corrected undirected graph (added missing symmetric connections)
    graph = {
        'Vienna': {'Milan', 'Vilnius', 'Lisbon', 'Riga', 'Rome', 'Oslo'},
        'Milan': {'Vienna', 'Riga', 'Oslo', 'Vilnius'},
        'Rome': {'Vienna', 'Oslo', 'Lisbon', 'Riga'},
        'Riga': {'Vienna', 'Milan', 'Oslo', 'Lisbon', 'Vilnius', 'Rome'},  # Added Rome
        'Vilnius': {'Vienna', 'Milan', 'Oslo', 'Riga'},  # Added Riga
        'Lisbon': {'Vienna', 'Riga', 'Rome', 'Oslo'},
        'Oslo': {'Riga', 'Rome', 'Vienna', 'Milan', 'Vilnius', 'Lisbon'}
    }
    
    cities = {
        'Vienna': 4,
        'Milan': 2,
        'Rome': 3,
        'Riga': 2,
        'Vilnius': 4,
        'Lisbon': 3,
        'Oslo': 3
    }
    
    middle_cities = ['Milan', 'Rome', 'Riga', 'Vilnius', 'Lisbon']
    
    for perm in itertools.permutations(middle_cities):
        seq = ['Vienna'] + list(perm) + ['Oslo']
        valid = True
        # Validate flight connections
        for i in range(len(seq) - 1):
            if seq[i+1] not in graph[seq[i]]:
                valid = False
                break
        if not valid:
            continue
            
        # Calculate start days correctly
        start_days = [1]  # Start day for first city
        for i in range(1, len(seq)):
            # Next city starts the day after previous city's stay ends
            start_days.append(start_days[i-1] + cities[seq[i-1]])
        
        # Check Lisbon constraint
        for idx, city in enumerate(seq):
            if city == 'Lisbon':
                start_day = start_days[idx]
                if start_day == 9:  # Must start on day 9 to cover 9-11
                    itinerary = []
                    for j in range(len(seq)):
                        start = start_days[j]
                        end = start + cities[seq[j]] - 1
                        day_range = f"Day {start}-{end}"
                        itinerary.append({"day_range": day_range, "place": seq[j]})
                    result = {'itinerary': itinerary}
                    print(json.dumps(result))
                    return
                    
    # No valid itinerary found
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()