import itertools
import json

def main():
    cities = ['Reykjavik', 'Istanbul', 'Edinburgh', 'Oslo', 'Stuttgart', 'Bucharest']
    
    graph = {
        'Bucharest': ['Oslo', 'Istanbul'],
        'Istanbul': ['Oslo', 'Bucharest', 'Edinburgh', 'Stuttgart'],
        'Reykjavik': ['Stuttgart', 'Oslo'],
        'Oslo': ['Bucharest', 'Istanbul', 'Reykjavik', 'Edinburgh'],
        'Stuttgart': ['Edinburgh', 'Istanbul'],
        'Edinburgh': ['Stuttgart', 'Istanbul', 'Oslo']
    }
    
    days_req = {
        'Reykjavik': 5,
        'Istanbul': 4,
        'Edinburgh': 5,
        'Oslo': 2,
        'Stuttgart': 3,
        'Bucharest': 5
    }
    
    for perm in itertools.permutations(cities):
        valid = True
        for i in range(len(perm) - 1):
            if perm[i+1] not in graph[perm[i]]:
                valid = False
                break
        if not valid:
            continue
            
        start_day = 1
        segments = []
        for city in perm:
            end_day = start_day + days_req[city] - 1
            segments.append((city, start_day, end_day))
            start_day = end_day
            
        istanbul_ok = False
        oslo_ok = False
        for city, s, e in segments:
            if city == 'Istanbul':
                if max(s, 5) <= min(e, 8):
                    istanbul_ok = True
            elif city == 'Oslo':
                if max(s, 8) <= min(e, 9):
                    oslo_ok = True
                    
        if istanbul_ok and oslo_ok:
            itinerary_list = []
            for city, s, e in segments:
                if s == e:
                    day_range = f"Day {s}"
                else:
                    day_range = f"Day {s}-{e}"
                itinerary_list.append({"day_range": day_range, "place": city})
                
            result = {"itinerary": itinerary_list}
            print(json.dumps(result))
            return
            
    print(json.dumps({"error": "No valid itinerary found"}))

if __name__ == "__main__":
    main()