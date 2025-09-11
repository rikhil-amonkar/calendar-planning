import itertools
import json

def main():
    cities = ['Porto', 'Geneva', 'Mykonos', 'Manchester', 'Hamburg', 'Naples', 'Frankfurt']
    req_days = {
        'Porto': 2,
        'Geneva': 3,
        'Mykonos': 3,
        'Manchester': 4,
        'Hamburg': 5,
        'Naples': 5,
        'Frankfurt': 2
    }
    
    graph = {
        'Hamburg': {'Frankfurt', 'Porto', 'Geneva', 'Manchester'},
        'Frankfurt': {'Hamburg', 'Geneva', 'Porto', 'Naples', 'Manchester'},
        'Naples': {'Mykonos', 'Manchester', 'Geneva', 'Frankfurt'},
        'Mykonos': {'Naples', 'Geneva'},
        'Geneva': {'Hamburg', 'Mykonos', 'Frankfurt', 'Porto', 'Manchester', 'Naples'},
        'Porto': {'Hamburg', 'Frankfurt', 'Geneva', 'Manchester'},
        'Manchester': {'Geneva', 'Naples', 'Frankfurt', 'Porto', 'Hamburg'}
    }
    
    for perm in itertools.permutations(cities):
        valid_path = True
        for i in range(len(perm) - 1):
            if perm[i+1] not in graph[perm[i]]:
                valid_path = False
                break
        if not valid_path:
            continue
            
        start_days = [0] * 7
        end_days = [0] * 7
        
        start_days[0] = 1
        end_days[0] = start_days[0] + req_days[perm[0]] - 1
        
        for i in range(1, 7):
            start_days[i] = end_days[i-1]
            end_days[i] = start_days[i] + req_days[perm[i]] - 1
        
        if end_days[6] != 18:
            continue
            
        frankfurt_index = perm.index('Frankfurt')
        mykonos_index = perm.index('Mykonos')
        manchester_index = perm.index('Manchester')
        
        frankfurt_ok = (start_days[frankfurt_index] <= 5 <= end_days[frankfurt_index] and 
                        start_days[frankfurt_index] <= 6 <= end_days[frankfurt_index])
        if not frankfurt_ok:
            continue
            
        mykonos_ok = False
        for d in range(10, 13):
            if start_days[mykonos_index] <= d <= end_days[mykonos_index]:
                mykonos_ok = True
                break
        if not mykonos_ok:
            continue
            
        manchester_ok = False
        for d in range(15, 19):
            if start_days[manchester_index] <= d <= end_days[manchester_index]:
                manchester_ok = True
                break
        if not manchester_ok:
            continue
            
        itinerary = []
        for i in range(7):
            day_range = f"Day {start_days[i]}-{end_days[i]}"
            itinerary.append({"day_range": day_range, "place": perm[i]})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
        return
    
    print('{"itinerary": []}')

if __name__ == "__main__":
    main()