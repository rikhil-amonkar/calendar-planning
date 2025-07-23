from z3 import *
import json

def main():
    cities = ['Vienna', 'Lyon', 'Amsterdam', 'Santorini']
    total_days_map = {
        'Vienna': 7,
        'Lyon': 3,
        'Amsterdam': 3,
        'Santorini': 4
    }
    
    start = { c: Int(f'start_{c}') for c in cities }
    end = { c: Int(f'end_{c}') for c in cities }
    
    s = Solver()
    
    for c in cities:
        s.add(start[c] >= 1)
        s.add(end[c] <= 14)
        s.add(end[c] - start[c] + 1 == total_days_map[c])
    
    s.add(start['Lyon'] == 7)
    s.add(end['Lyon'] == 9)
    s.add(start['Amsterdam'] == 9)
    s.add(end['Amsterdam'] == 11)
    
    s.add(start['Vienna'] == 1)
    s.add(end['Vienna'] == 7)
    s.add(start['Santorini'] == 11)
    s.add(end['Santorini'] == 14)
    
    s.add(end['Vienna'] == start['Lyon'])
    s.add(end['Lyon'] == start['Amsterdam'])
    s.add(end['Amsterdam'] == start['Santorini'])
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(1, 15):
            for city in cities:
                start_val = m.eval(start[city]).as_long()
                end_val = m.eval(end[city]).as_long()
                if day >= start_val and day <= end_val:
                    itinerary.append({"day": day, "city": city})
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()