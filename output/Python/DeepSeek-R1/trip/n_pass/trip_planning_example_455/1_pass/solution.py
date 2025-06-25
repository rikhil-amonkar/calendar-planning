import itertools
import json

def main():
    cities = ['Reykjavik', 'Riga', 'Warsaw', 'Istanbul', 'Krakow']
    durations = {
        'Reykjavik': 7,
        'Riga': 2,
        'Warsaw': 3,
        'Istanbul': 6,
        'Krakow': 7
    }
    graph = {
        'Istanbul': ['Krakow', 'Warsaw', 'Riga'],
        'Krakow': ['Istanbul', 'Warsaw'],
        'Warsaw': ['Reykjavik', 'Istanbul', 'Krakow', 'Riga'],
        'Riga': ['Istanbul', 'Warsaw'],
        'Reykjavik': ['Warsaw']
    }
    
    valid_itinerary = None
    for path in itertools.permutations(cities):
        valid_path = True
        for i in range(len(path) - 1):
            if path[i+1] not in graph[path[i]]:
                valid_path = False
                break
        if not valid_path:
            continue
        
        starts = []
        ends = []
        starts.append(1)
        ends.append(1 + durations[path[0]] - 1)
        for i in range(1, len(path)):
            start_next = ends[i-1]
            end_next = start_next + durations[path[i]] - 1
            starts.append(start_next)
            ends.append(end_next)
        
        if ends[-1] != 21:
            continue
            
        idx_riga = path.index('Riga')
        if starts[idx_riga] > 2:
            continue
            
        idx_istanbul = path.index('Istanbul')
        if starts[idx_istanbul] > 7 or ends[idx_istanbul] < 2:
            continue
            
        valid_itinerary = (path, starts, ends)
        break
    
    if valid_itinerary is None:
        result = {"itinerary": []}
    else:
        path, starts, ends = valid_itinerary
        itinerary_list = []
        for i in range(len(path)):
            day_range_str = f"Day {starts[i]}-{ends[i]}"
            itinerary_list.append({"day_range": day_range_str, "place": path[i]})
        result = {"itinerary": itinerary_list}
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()