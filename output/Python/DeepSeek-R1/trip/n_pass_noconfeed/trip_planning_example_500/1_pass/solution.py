import itertools
import json

def main():
    directed_flights = {
        'Split': ['Munich', 'Lyon', 'Hamburg'],
        'Munich': ['Split', 'Manchester', 'Hamburg', 'Lyon'],
        'Manchester': ['Munich', 'Hamburg', 'Split'],
        'Hamburg': ['Manchester', 'Munich', 'Split'],
        'Lyon': ['Split', 'Munich']
    }
    
    days_req = {
        'Hamburg': 7,
        'Munich': 6,
        'Lyon': 2,
        'Split': 7,
        'Manchester': 2
    }
    
    non_manchester = ['Hamburg', 'Munich', 'Lyon', 'Split']
    found = False
    result_itinerary = None
    
    for perm in itertools.permutations(non_manchester):
        seq = list(perm) + ['Manchester']
        valid = True
        for i in range(4):
            from_city = seq[i]
            to_city = seq[i+1]
            if to_city not in directed_flights[from_city]:
                valid = False
                break
        if not valid:
            continue
        
        d0 = days_req[seq[0]]
        d1 = days_req[seq[1]]
        d2 = days_req[seq[2]]
        d3 = days_req[seq[3]]
        
        start0 = 1
        end0 = start0 + d0 - 1
        start1 = end0
        end1 = start1 + d1 - 1
        start2 = end1
        end2 = start2 + d2 - 1
        start3 = end2
        end3 = start3 + d3 - 1
        start4 = end3
        end4 = start4 + days_req['Manchester'] - 1
        
        if end4 != 20:
            continue
        
        lyon_index = None
        for idx, city in enumerate(seq[:4]):
            if city == 'Lyon':
                lyon_index = idx
                break
        if lyon_index is None:
            continue
        
        if lyon_index == 0:
            lyon_start = start0
        elif lyon_index == 1:
            lyon_start = start1
        elif lyon_index == 2:
            lyon_start = start2
        elif lyon_index == 3:
            lyon_start = start3
        
        if lyon_start != 13:
            continue
        
        found = True
        itinerary = []
        for i in range(5):
            if i == 0:
                s = start0
                e = end0
            elif i == 1:
                s = start1
                e = end1
            elif i == 2:
                s = start2
                e = end2
            elif i == 3:
                s = start3
                e = end3
            else:
                s = start4
                e = end4
            day_range = f"Day {s}-{e}" if s != e else f"Day {s}"
            itinerary.append({"day_range": day_range, "place": seq[i]})
        result_itinerary = itinerary
        break
    
    if not found:
        print('{"error": "No valid itinerary found."}')
    else:
        print(json.dumps({"itinerary": result_itinerary}))

if __name__ == "__main__":
    main()