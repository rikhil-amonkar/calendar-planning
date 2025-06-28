import itertools
import json

def main():
    cities = ['Dublin', 'Madrid', 'Oslo', 'Vilnius', 'London', 'Berlin']
    durations = {
        'Dublin': 3,
        'Madrid': 2,
        'Oslo': 3,
        'Vilnius': 3,
        'London': 2,
        'Berlin': 5
    }
    
    graph = {
        'London': ['Madrid', 'Oslo', 'Dublin', 'Berlin'],
        'Madrid': ['London', 'Oslo', 'Dublin', 'Berlin'],
        'Oslo': ['Vilnius', 'Madrid', 'London', 'Berlin', 'Dublin'],
        'Vilnius': ['Oslo', 'Berlin'],
        'Berlin': ['Vilnius', 'Oslo', 'Madrid', 'London', 'Dublin'],
        'Dublin': ['Madrid', 'Oslo', 'London', 'Berlin']
    }
    
    found = False
    result_itinerary = None
    
    for perm in itertools.permutations(cities):
        valid_flight = True
        for i in range(len(perm)-1):
            if perm[i+1] not in graph[perm[i]]:
                valid_flight = False
                break
        if not valid_flight:
            continue
        
        starts = []
        ends = []
        current_start = 1
        for city in perm:
            dur = durations[city]
            end_day = current_start + dur - 1
            starts.append(current_start)
            ends.append(end_day)
            current_start = end_day + 1
        
        if ends[-1] != 13:
            continue
        
        idx_madrid = perm.index('Madrid')
        if starts[idx_madrid] > 3:
            continue
        
        idx_dublin = perm.index('Dublin')
        if starts[idx_dublin] < 5 or starts[idx_dublin] > 9:
            continue
        
        idx_berlin = perm.index('Berlin')
        if starts[idx_berlin] > 7:
            continue
        
        itinerary_list = []
        for i in range(len(perm)):
            day_range_str = f"Day {starts[i]}-{ends[i]}"
            itinerary_list.append({"day_range": day_range_str, "place": perm[i]})
        
        result_itinerary = {"itinerary": itinerary_list}
        found = True
        break
    
    if found:
        print(json.dumps(result_itinerary))
    else:
        print(json.dumps({"error": "No valid itinerary found."}))

if __name__ == "__main__":
    main()