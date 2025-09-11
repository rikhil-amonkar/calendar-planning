import itertools
import json

def main():
    cities = ['Brussels', 'Bucharest', 'Stuttgart', 'Mykonos', 'Helsinki', 'Split', 'London']
    madrid = 'Madrid'
    stuttgart = 'Stuttgart'
    
    required_days = {
        'Brussels': 4,
        'Bucharest': 3,
        'Stuttgart': 4,
        'Mykonos': 2,
        'Madrid': 2,
        'Helsinki': 5,
        'Split': 3,
        'London': 5
    }
    
    graph = {
        'Helsinki': {'London', 'Madrid', 'Split', 'Brussels'},
        'Split': {'Madrid', 'Helsinki', 'London', 'Stuttgart'},
        'Madrid': {'Split', 'Helsinki', 'London', 'Bucharest', 'Mykonos', 'Brussels'},
        'London': {'Helsinki', 'Madrid', 'Brussels', 'Bucharest', 'Mykonos', 'Split', 'Stuttgart'},
        'Brussels': {'London', 'Bucharest', 'Helsinki', 'Madrid'},
        'Bucharest': {'London', 'Brussels', 'Madrid'},
        'Mykonos': {'Madrid', 'London'},
        'Stuttgart': {'London', 'Split'}
    }
    
    for perm in itertools.permutations(cities):
        sequence = list(perm) + [madrid]
        if sequence.index(stuttgart) >= 4:
            continue
            
        valid = True
        for i in range(len(sequence) - 1):
            if sequence[i+1] not in graph[sequence[i]]:
                valid = False
                break
                
        if valid:
            break
    else:
        sequence = None
        
    if sequence is None:
        print('{"itinerary": []}')
        return
        
    itinerary = []
    start = 1
    for i, city in enumerate(sequence):
        if i < len(sequence) - 1:
            end = start + required_days[city] - 1
        else:
            end = start + required_days[city] - 2
        itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
        start = end + 1
        
    print(json.dumps({"itinerary": itinerary}))
    
if __name__ == '__main__':
    main()