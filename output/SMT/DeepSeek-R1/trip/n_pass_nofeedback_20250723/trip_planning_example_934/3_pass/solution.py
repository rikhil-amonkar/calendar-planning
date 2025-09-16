from z3 import *
import json

def main():
    cities = ['Brussels', 'Rome', 'Dubrovnik', 'Geneva', 'Budapest', 'Riga', 'Valencia']
    req_days = [5, 2, 3, 5, 2, 4, 2]
    
    bidirectional_pairs = [
        ('Brussels', 'Valencia'),
        ('Rome', 'Valencia'),
        ('Brussels', 'Geneva'),
        ('Rome', 'Geneva'),
        ('Dubrovnik', 'Geneva'),
        ('Valencia', 'Geneva'),
        ('Geneva', 'Budapest'),
        ('Riga', 'Brussels'),
        ('Rome', 'Budapest'),
        ('Rome', 'Brussels'),
        ('Brussels', 'Budapest'),
        ('Dubrovnik', 'Rome')
    ]
    directed_edges = [('Rome', 'Riga')]
    
    edges = set()
    for a, b in bidirectional_pairs:
        i = cities.index(a)
        j = cities.index(b)
        edges.add((i, j))
        edges.add((j, i))
    for a, b in directed_edges:
        i = cities.index(a)
        j = cities.index(b)
        edges.add((i, j))
    
    num_days = 17
    s = Solver()
    
    start = [Int(f'start_{d}') for d in range(num_days)]
    flight = [Int(f'flight_{d}') for d in range(num_days)]
    NO_FLIGHT = 7
    
    for d in range(num_days):
        s.add(0 <= start[d], start[d] <= 6)
        s.add(0 <= flight[d], flight[d] <= 7)
        s.add(If(flight[d] != NO_FLIGHT, flight[d] != start[d], True))
    
    for d in range(num_days):
        cond = (flight[d] != NO_FLIGHT)
        allowed = []
        for (i, j) in edges:
            allowed.append(And(start[d] == i, flight[d] == j))
        s.add(If(cond, Or(allowed), True))
    
    for d in range(num_days - 1):
        s.add(If(flight[d] != NO_FLIGHT, start[d+1] == flight[d], start[d+1] == start[d]))
    
    for c in range(7):
        total = 0
        for d in range(num_days):
            in_city = Or(start[d] == c, And(flight[d] != NO_FLIGHT, flight[d] == c))
            total += If(in_city, 1, 0)
        s.add(total == req_days[c])
    
    brussels_idx = cities.index('Brussels')
    brussels_constraint = Or([Or(start[d] == brussels_idx, And(flight[d] != NO_FLIGHT, flight[d] == brussels_idx)) for d in [6,7,8,9,10]])
    s.add(brussels_constraint)
    
    riga_idx = cities.index('Riga')
    riga_constraint = Or([Or(start[d] == riga_idx, And(flight[d] != NO_FLIGHT, flight[d] == riga_idx)) for d in [3,4,5,6]])
    s.add(riga_constraint)
    
    budapest_idx = cities.index('Budapest')
    budapest_constraint = Or([Or(start[d] == budapest_idx, And(flight[d] != NO_FLIGHT, flight[d] == budapest_idx)) for d in [15,16]])
    s.add(budapest_constraint)
    
    flight_count = Sum([If(flight[d] != NO_FLIGHT, 1, 0) for d in range(num_days)])
    s.add(flight_count == 6)
    
    if s.check() == sat:
        model = s.model()
        itinerary_days = []
        for d in range(num_days):
            s_val = model.evaluate(start[d]).as_long()
            f_val = model.evaluate(flight[d]).as_long()
            start_city = cities[s_val]
            if f_val == NO_FLIGHT:
                places = [start_city]
            else:
                flight_city = cities[f_val]
                places = [start_city, flight_city]
            itinerary_days.append({"day": d+1, "place": places})
        
        blocks = []
        d = 0
        num_days = len(itinerary_days)
        while d < num_days:
            start_city = itinerary_days[d]['place'][0]
            j = d
            while j < num_days:
                if itinerary_days[j]['place'][0] != start_city:
                    break
                if j < num_days - 1:
                    if len(itinerary_days[j]['place']) > 1:
                        j += 1
                        break
                j += 1
            else:
                j = num_days
            start_day_1idx = d + 1
            end_day_1idx = j
            if j - d == 1:
                day_range_str = f"Day {start_day_1idx}"
            else:
                day_range_str = f"Day {start_day_1idx}-{end_day_1idx}"
            blocks.append({'day_range': day_range_str, 'place': start_city})
            d = j
        
        result = {"itinerary": blocks}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()