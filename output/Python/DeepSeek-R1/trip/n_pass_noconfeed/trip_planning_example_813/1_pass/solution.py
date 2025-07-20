import itertools
import json

def main():
    graph = {
        'Frankfurt': ['Dublin', 'London', 'Vilnius', 'Stuttgart'],
        'Dublin': ['Frankfurt', 'London', 'Seville', 'Santorini'],
        'London': ['Frankfurt', 'Dublin', 'Santorini', 'Stuttgart'],
        'Vilnius': ['Frankfurt'],
        'Stuttgart': ['Frankfurt', 'London'],
        'Seville': ['Dublin'],
        'Santorini': ['London', 'Dublin']
    }
    
    days_req = {
        'Seville': 5,
        'Vilnius': 3,
        'Santorini': 2,
        'London': 2,
        'Stuttgart': 3,
        'Dublin': 3,
        'Frankfurt': 5
    }
    
    cities = list(days_req.keys())
    found = False
    result_itinerary = None
    
    for perm in itertools.permutations(cities):
        valid_flight = True
        for i in range(6):
            if perm[i+1] not in graph[perm[i]]:
                valid_flight = False
                break
        if not valid_flight:
            continue
        
        current_start = 1
        valid_constraint = True
        for idx, city in enumerate(perm):
            if idx < 6:
                duration = days_req[city]
                end_day = current_start + duration - 1
            else:
                duration = 17 - current_start + 1
                end_day = 17
            
            if city == 'London':
                if idx < 6:
                    if not ((current_start <= 9 <= end_day) or (current_start <= 10 <= end_day)):
                        valid_constraint = False
                        break
                else:
                    valid_constraint = False
                    break
            
            if city == 'Stuttgart':
                if idx < 6:
                    if end_day < 7 or current_start > 9:
                        valid_constraint = False
                        break
                else:
                    valid_constraint = False
                    break
            
            if idx < 6:
                current_start = end_day
        
        if not valid_constraint:
            continue
        
        itinerary_list = []
        current = 1
        for i, city in enumerate(perm):
            if i < 6:
                duration = days_req[city]
                end = current + duration - 1
                if current == end:
                    day_range = f"Day {current}"
                else:
                    day_range = f"Day {current}-{end}"
                itinerary_list.append({"day_range": day_range, "place": city})
                current = end
            else:
                if current == 17:
                    day_range = f"Day 17"
                else:
                    day_range = f"Day {current}-17"
                itinerary_list.append({"day_range": day_range, "place": city})
        
        result_itinerary = {"itinerary": itinerary_list}
        found = True
        break
    
    if not found:
        result_itinerary = {"itinerary": []}
    
    print(json.dumps(result_itinerary))

if __name__ == "__main__":
    main()