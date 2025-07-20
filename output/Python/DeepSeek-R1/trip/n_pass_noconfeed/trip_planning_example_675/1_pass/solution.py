import itertools
import json

def main():
    cities = ['Dubrovnik', 'Split', 'Milan', 'Porto', 'Krakow', 'Munich']
    required_days = {
        'Dubrovnik': 4,
        'Split': 3,
        'Milan': 3,
        'Porto': 4,
        'Krakow': 2,
        'Munich': 5
    }
    
    flight_connections = [
        ('Munich', 'Porto'),
        ('Split', 'Milan'),
        ('Milan', 'Porto'),
        ('Munich', 'Krakow'),
        ('Munich', 'Milan'),
        ('Dubrovnik', 'Munich'),
        ('Krakow', 'Split'),
        ('Krakow', 'Milan'),
        ('Munich', 'Split')
    ]
    
    graph = {city: set() for city in cities}
    for city1, city2 in flight_connections:
        graph[city1].add(city2)
        graph[city2].add(city1)
    
    valid_itinerary = None
    for perm in itertools.permutations(cities):
        valid_route = True
        for i in range(len(perm) - 1):
            if perm[i+1] not in graph[perm[i]]:
                valid_route = False
                break
        if not valid_route:
            continue
        
        flight_days = [0] * 5
        flight_days[0] = required_days[perm[0]]
        flight_days[1] = flight_days[0] + required_days[perm[1]] - 1
        flight_days[2] = flight_days[1] + required_days[perm[2]] - 1
        flight_days[3] = flight_days[2] + required_days[perm[3]] - 1
        flight_days[4] = flight_days[3] + required_days[perm[4]] - 1
        
        blocks = {
            perm[0]: (1, flight_days[0]),
            perm[1]: (flight_days[0], flight_days[1]),
            perm[2]: (flight_days[1], flight_days[2]),
            perm[3]: (flight_days[2], flight_days[3]),
            perm[4]: (flight_days[3], flight_days[4]),
            perm[5]: (flight_days[4], 16)
        }
        
        munich_start, munich_end = blocks['Munich']
        if not (munich_start <= 8 and munich_end >= 4):
            continue
            
        krakow_start, krakow_end = blocks['Krakow']
        if not (krakow_start <= 9 and krakow_end >= 8):
            continue
            
        milan_start, milan_end = blocks['Milan']
        if not (milan_start <= 13 and milan_end >= 11):
            continue
            
        itinerary_list = []
        ranges = [1, flight_days[0], flight_days[1], flight_days[2], flight_days[3], flight_days[4], 16]
        for i in range(6):
            start = ranges[i]
            end = ranges[i+1]
            if start == end:
                day_range_str = f"Day {start}"
            else:
                day_range_str = f"Day {start}-{end}"
            itinerary_list.append({"day_range": day_range_str, "place": perm[i]})
        
        valid_itinerary = itinerary_list
        break
        
    if valid_itinerary is None:
        result = {"itinerary": []}
    else:
        result = {"itinerary": valid_itinerary}
        
    print(json.dumps(result))

if __name__ == "__main__":
    main()