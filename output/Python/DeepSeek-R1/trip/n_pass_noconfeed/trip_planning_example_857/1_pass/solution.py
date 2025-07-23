import itertools
import json

def main():
    cities = ['Porto', 'Geneva', 'Mykonos', 'Manchester', 'Hamburg', 'Naples', 'Frankfurt']
    durations = {
        'Porto': 2,
        'Geneva': 3,
        'Mykonos': 3,
        'Manchester': 4,
        'Hamburg': 5,
        'Naples': 5,
        'Frankfurt': 2
    }
    
    graph = {
        'Hamburg': set(['Frankfurt', 'Porto', 'Geneva', 'Manchester']),
        'Naples': set(['Mykonos', 'Manchester', 'Frankfurt', 'Geneva']),
        'Mykonos': set(['Naples', 'Geneva']),
        'Frankfurt': set(['Hamburg', 'Geneva', 'Porto', 'Naples', 'Manchester']),
        'Geneva': set(['Hamburg', 'Mykonos', 'Frankfurt', 'Porto', 'Manchester', 'Naples']),
        'Porto': set(['Hamburg', 'Frankfurt', 'Geneva', 'Manchester']),
        'Manchester': set(['Geneva', 'Naples', 'Frankfurt', 'Porto', 'Hamburg'])
    }
    
    found = False
    result_itinerary = None
    
    for order in itertools.permutations(cities):
        valid_order = True
        for i in range(len(order)-1):
            if order[i+1] not in graph[order[i]]:
                valid_order = False
                break
        if not valid_order:
            continue
            
        stays = []
        for idx, city in enumerate(order):
            if idx == 0:
                start = 1
            else:
                start = stays[-1][1]
            end = start + durations[city] - 1
            stays.append((start, end))
        
        city_stay = {city: stay for city, stay in zip(order, stays)}
        
        s_myk, e_myk = city_stay['Mykonos']
        if not (s_myk <= 12 and e_myk >= 10):
            continue
            
        s_man, e_man = city_stay['Manchester']
        if not (s_man <= 18 and e_man >= 15):
            continue
            
        s_frank, e_frank = city_stay['Frankfurt']
        if not (s_frank <= 6 and e_frank >= 5):
            continue
            
        itinerary_list = []
        for i in range(len(order)):
            s, e = stays[i]
            day_range_str = f"Day {s}-{e}"
            itinerary_list.append({
                "day_range": day_range_str,
                "place": order[i]
            })
        result_itinerary = {"itinerary": itinerary_list}
        found = True
        break
        
    if not found:
        result_itinerary = {"itinerary": []}
    
    print(json.dumps(result_itinerary))

if __name__ == "__main__":
    main()