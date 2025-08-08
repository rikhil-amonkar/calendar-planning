from z3 import Solver, Int, sat
import json

def main():
    cities = ["Santorini", "Valencia", "Madrid", "Seville", "Bucharest", "Vienna", "Riga", "Tallinn", "Krakow", "Frankfurt"]
    req_days = {
        "Santorini": 3,
        "Valencia": 4,
        "Madrid": 2,
        "Seville": 2,
        "Bucharest": 3,
        "Vienna": 4,
        "Riga": 4,
        "Tallinn": 5,
        "Krakow": 5,
        "Frankfurt": 4
    }
    
    start = {c: Int(f'start_{c}') for c in cities}
    end = {c: Int(f'end_{c}') for c in cities}
    
    fixed = {
        "Vienna": (3, 6),
        "Madrid": (6, 7),
        "Riga": (20, 23),
        "Tallinn": (23, 27),
        "Krakow": (11, 15)
    }
    
    sequence = [
        "Santorini",
        "Vienna",
        "Madrid",
        "Seville",
        "Valencia",
        "Krakow",
        "Frankfurt",
        "Bucharest",
        "Riga",
        "Tallinn"
    ]
    
    s = Solver()
    
    for city, (s_val, e_val) in fixed.items():
        s.add(start[city] == s_val)
        s.add(end[city] == e_val)
    
    for city in cities:
        s.add(end[city] - start[city] + 1 == req_days[city])
    
    for i in range(len(sequence) - 1):
        s.add(end[sequence[i]] == start[sequence[i+1]])
    
    s.add(start[sequence[0]] == 1)
    s.add(end[sequence[-1]] == 27)
    
    if s.check() == sat:
        m = s.model()
        itinerary_list = []
        for day in range(1, 28):
            for city in cities:
                start_val = m.eval(start[city]).as_long()
                end_val = m.eval(end[city]).as_long()
                if start_val <= day <= end_val:
                    itinerary_list.append({"day": day, "city": city})
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()