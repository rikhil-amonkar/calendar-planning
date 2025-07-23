import itertools
import json

def main():
    req_days = {
        'Reykjavik': 2,
        'Warsaw': 3,
        'Madrid': 4,
        'Split': 4,
        'Budapest': 4
    }
    
    graph = {
        'Helsinki': ['Reykjavik', 'Split', 'Madrid', 'Budapest', 'Warsaw'],
        'Reykjavik': ['Helsinki', 'Warsaw', 'Budapest', 'Madrid'],
        'Warsaw': ['Budapest', 'Reykjavik', 'Helsinki', 'Split', 'Madrid'],
        'Split': ['Madrid', 'Helsinki', 'Warsaw'],
        'Budapest': ['Warsaw', 'Helsinki', 'Reykjavik', 'Madrid'],
        'Madrid': ['Split', 'Helsinki', 'Warsaw', 'Budapest']
    }
    
    cities_after = ['Reykjavik', 'Warsaw', 'Madrid', 'Split', 'Budapest']
    start_day_after_helsinki = 2
    total_days = 14
    valid_itinerary = None
    
    for perm in itertools.permutations(cities_after):
        current_city = 'Helsinki'
        current_day = start_day_after_helsinki
        itinerary_after = []
        valid = True
        for city in perm:
            if city not in graph[current_city]:
                valid = False
                break
            duration = req_days[city]
            start_d = current_day
            end_d = start_d + duration - 1
            itinerary_after.append((start_d, end_d, city))
            current_day = end_d
            current_city = city
        
        if not valid:
            continue
        
        if current_day != total_days:
            continue
        
        reykjavik_constraint = False
        warsaw_constraint = False
        for (s, e, city) in itinerary_after:
            if city == 'Reykjavik':
                if 7 <= s <= 9:
                    reykjavik_constraint = True
            if city == 'Warsaw':
                if s <= 11 and e >= 9:
                    warsaw_constraint = True
        
        if reykjavik_constraint and warsaw_constraint:
            full_itinerary = [(1, 2, 'Helsinki')]
            full_itinerary.extend(itinerary_after)
            result_list = []
            for (start_d, end_d, city) in full_itinerary:
                day_range_str = f"Day {start_d}-{end_d}"
                result_list.append({"day_range": day_range_str, "place": city})
            valid_itinerary = result_list
            break
    
    if valid_itinerary is None:
        output_json = json.dumps({"itinerary": []})
    else:
        output_json = json.dumps({"itinerary": valid_itinerary})
    print(output_json)

if __name__ == "__main__":
    main()