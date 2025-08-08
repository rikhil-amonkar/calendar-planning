import json
from z3 import Solver, Int, sat

def main():
    s = Solver()
    cities = ['Dubrovnik', 'Split', 'Milan', 'Porto', 'Krakow', 'Munich']
    start = {c: Int(f'start_{c}') for c in cities}
    end = {c: Int(f'end_{c}') for c in cities}
    
    stays = {
        'Dubrovnik': 4,
        'Split': 3,
        'Milan': 3,
        'Porto': 4,
        'Krakow': 2,
        'Munich': 5
    }
    
    s.add(start['Munich'] == 4)
    s.add(end['Munich'] == 8)
    s.add(start['Krakow'] == 8)
    s.add(end['Krakow'] == 9)
    s.add(start['Milan'] == 11)
    s.add(end['Milan'] == 13)
    
    for c in cities:
        s.add(end[c] - start[c] + 1 == stays[c])
        s.add(start[c] >= 1, start[c] <= 16)
        s.add(end[c] >= start[c], end[c] <= 16)
    
    order = ['Dubrovnik', 'Munich', 'Krakow', 'Split', 'Milan', 'Porto']
    for i in range(len(order) - 1):
        s.add(end[order[i]] == start[order[i+1]])
    
    s.add(start['Dubrovnik'] == 1)
    s.add(end['Porto'] == 16)
    
    if s.check() == sat:
        m = s.model()
        starts_val = {}
        ends_val = {}
        for c in cities:
            starts_val[c] = m[start[c]].as_long()
            ends_val[c] = m[end[c]].as_long()
        
        rev_order = list(reversed(order))
        itinerary = []
        for d in range(1, 17):
            for c in rev_order:
                if starts_val[c] <= d <= ends_val[c]:
                    itinerary.append({"day": d, "place": c})
                    break
        
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == '__main__':
    main()