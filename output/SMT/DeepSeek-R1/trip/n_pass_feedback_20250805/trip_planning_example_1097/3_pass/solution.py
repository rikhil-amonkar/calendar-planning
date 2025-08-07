from z3 import *
import json

def main():
    cities = ['Reykjavik', 'Riga', 'Oslo', 'Lyon', 'Dubrovnik', 'Madrid', 'Warsaw', 'London']
    required_days = [4, 2, 3, 5, 2, 2, 4, 3]
    
    edges = [
        (0, 6), (2, 5), (6, 1), (3, 7), (5, 7), (6, 7), (0, 5), (6, 2), (2, 4),
        (0, 2), (1, 2), (2, 3), (2, 7), (0, 7), (6, 5), (5, 3), (4, 5)
    ]
    flights_set = set()
    for a, b in edges:
        if a > b:
            flights_set.add((b, a))
        else:
            flights_set.add((a, b))
    
    n_days = 18
    n_cities = len(cities)
    s = Solver()
    day_end = [Int(f'day_{i}') for i in range(n_days)]
    
    for i in range(n_days):
        s.add(day_end[i] >= 0, day_end[i] < n_cities)
    
    for i in range(n_days - 1):
        a = day_end[i]
        b = day_end[i + 1]
        conds = []
        for (c1, c2) in flights_set:
            conds.append(And(a == c1, b == c2))
            conds.append(And(a == c2, b == c1))
        s.add(Or(a == b, Or(conds)))
    
    for c in range(n_cities):
        total = If(day_end[0] == c, 1, 0)
        for i in range(1, n_days):
            same_city = (day_end[i-1] == day_end[i])
            count_day = If(same_city, 
                          If(day_end[i] == c, 1, 0),
                          If(day_end[i-1] == c, 1, 0) + If(day_end[i] == c, 1, 0))
            total += count_day
        s.add(total == required_days[c])
    
    # Riga (index1) on day4 (index3) or day5 (index4)
    in_riga_day4 = Or(day_end[2] == 1, day_end[3] == 1)
    in_riga_day5 = Or(day_end[3] == 1, day_end[4] == 1)
    s.add(Or(in_riga_day4, in_riga_day5))
    
    # Dubrovnik (index4) on day7 (index6) or day8 (index7)
    in_dubrovnik_day7 = Or(day_end[5] == 4, day_end[6] == 4)
    in_dubrovnik_day8 = Or(day_end[6] == 4, day_end[7] == 4)
    s.add(Or(in_dubrovnik_day7, in_dubrovnik_day8))
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        d0_val = m.evaluate(day_end[0]).as_long()
        itinerary.append([cities[d0_val]])
        for i in range(1, n_days):
            prev_val = m.evaluate(day_end[i-1]).as_long()
            curr_val = m.evaluate(day_end[i]).as_long()
            if prev_val == curr_val:
                itinerary.append([cities[curr_val]])
            else:
                itinerary.append([cities[prev_val], cities[curr_val]])
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()