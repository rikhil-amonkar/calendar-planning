import json
from itertools import permutations

def main():
    total_days = 16
    days_req = {
        'Bucharest': 7,
        'Lyon': 7,
        'Porto': 4
    }
    wedding_min_day = 1
    wedding_max_day = 7
    
    graph = {
        'Bucharest': ['Lyon'],
        'Lyon': ['Bucharest', 'Porto'],
        'Porto': ['Lyon']
    }
    
    cities = list(days_req.keys())
    valid_itinerary = None
    
    for order in permutations(cities):
        connected = True
        for i in range(len(order) - 1):
            if order[i+1] not in graph[order[i]]:
                connected = False
                break
        if not connected:
            continue
            
        seg1_end = days_req[order[0]]
        seg2_end = seg1_end + days_req[order[1]] - 1
        seg3_end = total_days
        
        if seg3_end - seg2_end + 1 != days_req[order[2]]:
            continue
            
        wedding_ok = False
        segments = [
            (1, seg1_end, order[0]),
            (seg1_end, seg2_end, order[1]),
            (seg2_end, seg3_end, order[2])
        ]
        for start, end, city in segments:
            if city == 'Bucharest' and start <= wedding_max_day:
                wedding_ok = True
                break
                
        if wedding_ok:
            valid_itinerary = segments
            break
            
    if valid_itinerary is None:
        print(json.dumps({"itinerary": []}))
        return
        
    itinerary_list = []
    for start, end, city in valid_itinerary:
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        itinerary_list.append({"day_range": day_range, "place": city})
        
    print(json.dumps({"itinerary": itinerary_list}))

if __name__ == "__main__":
    main()