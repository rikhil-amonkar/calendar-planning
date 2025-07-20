import itertools
import json

def main():
    total_days = 7
    city_days = {
        'Madrid': 4,
        'Dublin': 3,
        'Tallinn': 2
    }
    workshop_city = 'Tallinn'
    workshop_day_range = (6, 7)
    direct_flights = [('Madrid', 'Dublin'), ('Dublin', 'Tallinn')]
    
    cities = list(city_days.keys())
    valid_paths = []
    for path in itertools.permutations(cities):
        if path[-1] != workshop_city:
            continue
        valid = True
        for i in range(len(path) - 1):
            if (path[i], path[i+1]) not in direct_flights and (path[i+1], path[i]) not in direct_flights:
                valid = False
                break
        if valid:
            valid_paths.append(path)
    
    if not valid_paths:
        print(json.dumps({"itinerary": []}))
        return
    
    city_sequence = valid_paths[0]
    starts = []
    ends = []
    itinerary_list = []
    
    for i, city in enumerate(city_sequence):
        if i == 0:
            start = 1
        else:
            start = ends[i-1]
        duration = city_days[city]
        end = start + duration - 1
        starts.append(start)
        ends.append(end)
        
        if start == end:
            day_range_str = f"Day {start}"
        else:
            day_range_str = f"Day {start}-{end}"
        itinerary_list.append({"day_range": day_range_str, "place": city})
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()