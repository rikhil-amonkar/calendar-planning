import itertools
import json

def main():
    cities = ['Seville', 'Vilnius', 'Santorini', 'London', 'Stuttgart', 'Dublin', 'Frankfurt']
    req = {
        'Seville': 5,
        'Vilnius': 3,
        'Santorini': 2,
        'London': 2,
        'Stuttgart': 3,
        'Dublin': 3,
        'Frankfurt': 5
    }
    
    graph = {
        'Frankfurt': ['Dublin', 'London', 'Vilnius', 'Stuttgart'],
        'Dublin': ['Frankfurt', 'London', 'Seville', 'Santorini'],
        'London': ['Frankfurt', 'Dublin', 'Santorini', 'Stuttgart'],
        'Vilnius': ['Frankfurt'],
        'Stuttgart': ['Frankfurt', 'London'],
        'Seville': ['Dublin'],
        'Santorini': ['London', 'Dublin']
    }
    
    for perm in itertools.permutations(cities):
        # Check flight connections
        valid_connection = True
        for i in range(len(perm) - 1):
            if perm[i+1] not in graph[perm[i]]:
                valid_connection = False
                break
        if not valid_connection:
            continue
            
        # Compute transition days
        t = [0] * 6
        try:
            t[0] = req[perm[0]]
            for i in range(1, 6):
                t[i] = t[i-1] + req[perm[i]] - 1
                if t[i] < 1 or t[i] > 17:
                    raise ValueError("Invalid transition day")
        except:
            continue
            
        # Check last city constraint
        if t[5] != 18 - req[perm[6]]:
            continue
            
        # Check Stuttgart constraints
        stuttgart_index = perm.index('Stuttgart')
        stuttgart_start = 1 if stuttgart_index == 0 else t[stuttgart_index-1]
        stuttgart_end = t[stuttgart_index]
        if not (stuttgart_start <= 7 and stuttgart_end >= 9):
            continue
            
        # Check London constraints
        london_index = perm.index('London')
        london_start = 1 if london_index == 0 else t[london_index-1]
        london_end = t[london_index]
        if not (london_start <= 10 and london_end >= 9):
            continue
            
        # Build itinerary
        itinerary = []
        start_day = 1
        for i in range(6):
            end_day = t[i]
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": perm[i]
            })
            start_day = end_day
        itinerary.append({
            "day_range": f"Day {start_day}-17",
            "place": perm[6]
        })
        
        print(json.dumps({"itinerary": itinerary}, indent=2))
        return
        
    print('{"itinerary": []}')

if __name__ == "__main__":
    main()