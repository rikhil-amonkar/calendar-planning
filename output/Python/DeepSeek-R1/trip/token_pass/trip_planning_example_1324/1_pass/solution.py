import json
from itertools import permutations

def main():
    cities = ['Venice', 'Barcelona', 'Copenhagen', 'Lyon', 'Reykjavik', 'Dubrovnik', 'Athens', 'Tallinn', 'Munich']
    
    days_dict = {
        'Venice': 4,
        'Barcelona': 3,
        'Copenhagen': 4,
        'Lyon': 4,
        'Reykjavik': 4,
        'Dubrovnik': 5,
        'Athens': 2,
        'Tallinn': 5,
        'Munich': 3
    }
    
    graph = {
        'Copenhagen': {'Athens', 'Dubrovnik', 'Munich', 'Reykjavik', 'Venice', 'Barcelona', 'Tallinn'},
        'Munich': {'Tallinn', 'Copenhagen', 'Venice', 'Reykjavik', 'Athens', 'Lyon', 'Dubrovnik', 'Barcelona'},
        'Venice': {'Munich', 'Athens', 'Copenhagen', 'Barcelona', 'Lyon'},
        'Reykjavik': {'Athens', 'Copenhagen', 'Munich', 'Barcelona'},
        'Athens': {'Copenhagen', 'Dubrovnik', 'Venice', 'Reykjavik', 'Munich', 'Barcelona'},
        'Dubrovnik': {'Copenhagen', 'Athens', 'Barcelona', 'Munich'},
        'Lyon': {'Barcelona', 'Munich', 'Venice'},
        'Barcelona': {'Lyon', 'Reykjavik', 'Dubrovnik', 'Athens', 'Copenhagen', 'Venice', 'Munich', 'Tallinn'},
        'Tallinn': {'Munich', 'Barcelona', 'Copenhagen'}
    }
    
    constraints = {
        'Barcelona': (10, 12),
        'Copenhagen': (7, 10),
        'Dubrovnik': (16, 20)
    }
    
    for path in permutations(cities):
        valid_path = True
        for i in range(len(path) - 1):
            if path[i+1] not in graph[path[i]]:
                valid_path = False
                break
        if not valid_path:
            continue
            
        start_days = [1]
        for i in range(len(path) - 1):
            start_days.append(start_days[i] + days_dict[path[i]] - 1)
            
        satisfies_constraints = True
        for city, (low, high) in constraints.items():
            idx = path.index(city)
            s = start_days[idx]
            e = s + days_dict[city] - 1
            if not (max(s, low) <= min(e, high)):
                satisfies_constraints = False
                break
                
        if satisfies_constraints:
            itinerary = []
            for i, city in enumerate(path):
                s = start_days[i]
                e = s + days_dict[city] - 1
                day_range = f"Day {s}-{e}" if s != e else f"Day {s}"
                itinerary.append({"day_range": day_range, "place": city})
            print(json.dumps({"itinerary": itinerary}, indent=2))
            return
            
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()