import json
import itertools

def main():
    dur = {
        'Bucharest': 6,
        'Warsaw': 2,
        'Stuttgart': 7,
        'Copenhagen': 3,
        'Dubrovnik': 5
    }
    total_days = 19
    start_city = 'Bucharest'
    other_cities = ['Warsaw', 'Stuttgart', 'Copenhagen', 'Dubrovnik']
    
    direct_flights = [
        ('Warsaw', 'Copenhagen'),
        ('Stuttgart', 'Copenhagen'),
        ('Warsaw', 'Stuttgart'),
        ('Bucharest', 'Copenhagen'),
        ('Bucharest', 'Warsaw'),
        ('Copenhagen', 'Dubrovnik')
    ]
    graph = {}
    for a, b in direct_flights:
        graph.setdefault(a, set()).add(b)
        graph.setdefault(b, set()).add(a)
    
    found = False
    result_segments = None
    
    for perm in itertools.permutations(other_cities):
        itinerary_cities = [start_city] + list(perm)
        valid = True
        for i in range(len(itinerary_cities) - 1):
            a = itinerary_cities[i]
            b = itinerary_cities[i+1]
            if a in graph and b in graph[a]:
                continue
            else:
                valid = False
                break
        if not valid:
            continue
        
        segments = []
        current_day = 1
        n = len(itinerary_cities)
        
        for idx, city in enumerate(itinerary_cities):
            if idx == n - 1:
                end_day = total_days
                duration_actual = end_day - current_day + 1
                if duration_actual != dur[city]:
                    valid = False
                    break
                segments.append((current_day, end_day, city))
            else:
                end_day = current_day + dur[city] - 1
                if end_day > total_days:
                    valid = False
                    break
                segments.append((current_day, end_day, city))
                current_day = end_day
        if not valid:
            continue
        
        stuttgart_ok = False
        for seg in segments:
            if seg[2] == 'Stuttgart':
                s, e, _ = seg
                if s <= 7 <= e and s <= 13 <= e:
                    stuttgart_ok = True
                    break
        if not stuttgart_ok:
            continue
        
        found = True
        result_segments = []
        for seg in segments:
            s, e, city = seg
            if s == e:
                day_range_str = f"Day {s}"
            else:
                day_range_str = f"Day {s}-{e}"
            result_segments.append({"day_range": day_range_str, "place": city})
        break
    
    if not found:
        result_segments = [{"day_range": "No valid itinerary found", "place": ""}]
    
    output_dict = {"itinerary": result_segments}
    print(json.dumps(output_dict))

if __name__ == '__main__':
    main()