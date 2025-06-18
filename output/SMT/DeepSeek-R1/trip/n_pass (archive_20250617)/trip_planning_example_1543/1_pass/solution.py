from z3 import *

def main():
    cities = ['Prague', 'Warsaw', 'Dublin', 'Athens', 'Vilnius', 'Porto', 'London', 'Seville', 'Lisbon', 'Dubrovnik']
    days_req = [3, 4, 3, 3, 4, 5, 3, 2, 5, 3]
    
    city_index = {city: idx for idx, city in enumerate(cities)}
    
    flight_list = [
        ('Warsaw', 'Vilnius'), ('Prague', 'Athens'), ('London', 'Lisbon'),
        ('Lisbon', 'Porto'), ('Prague', 'Lisbon'), ('London', 'Dublin'),
        ('Athens', 'Vilnius'), ('Athens', 'Dublin'), ('Prague', 'London'),
        ('London', 'Warsaw'), ('Dublin', 'Seville'), ('Seville', 'Porto'),
        ('Lisbon', 'Athens'), ('Dublin', 'Porto'), ('Athens', 'Warsaw'),
        ('Lisbon', 'Warsaw'), ('Porto', 'Warsaw'), ('Prague', 'Warsaw'),
        ('Prague', 'Dublin'), ('Athens', 'Dubrovnik'), ('Lisbon', 'Dublin'),
        ('Dubrovnik', 'Dublin'), ('Lisbon', 'Seville'), ('London', 'Athens')
    ]
    
    flight_set = set()
    for u, v in flight_list:
        i, j = city_index[u], city_index[v]
        flight_set.add((min(i, j), max(i, j)))
    
    n = len(cities)
    days_total = 26
    s = Solver()
    
    S = [Int(f'S_{i}') for i in range(n)]
    E = [Int(f'E_{i}') for i in range(n)]
    
    for i in range(n):
        s.add(E[i] == S[i] + days_req[i] - 1)
        s.add(S[i] >= 1)
        s.add(E[i] <= days_total)
    
    london_idx = city_index['London']
    porto_idx = city_index['Porto']
    s.add(S[london_idx] == 3)
    s.add(E[london_idx] == 5)
    s.add(S[porto_idx] == 16)
    s.add(E[porto_idx] == 20)
    
    prague_idx = city_index['Prague']
    warsaw_idx = city_index['Warsaw']
    lisbon_idx = city_index['Lisbon']
    
    s.add(Or(
        And(S[prague_idx] <= 1, E[prague_idx] >= 1),
        And(S[prague_idx] <= 2, E[prague_idx] >= 2),
        And(S[prague_idx] <= 3, E[prague_idx] >= 3)
    ))
    
    or_conds_warsaw = []
    for d in [20, 21, 22, 23]:
        or_conds_warsaw.append(And(S[warsaw_idx] <= d, E[warsaw_idx] >= d))
    s.add(Or(or_conds_warsaw))
    
    or_conds_lisbon = []
    for d in [5, 6, 7, 8, 9]:
        or_conds_lisbon.append(And(S[lisbon_idx] <= d, E[lisbon_idx] >= d))
    s.add(Or(or_conds_lisbon))
    
    for i in range(n):
        for j in range(i + 1, n):
            s.add(Or(
                E[i] < S[j],
                E[j] < S[i],
                E[i] == S[j],
                E[j] == S[i]
            ))
    
    for d in range(1, days_total + 1):
        s.add(Or([And(S[i] <= d, d <= E[i]) for i in range(n)]))
    
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            low, high = min(i, j), max(i, j)
            if (low, high) not in flight_set:
                s.add(And(E[i] != S[j], E[j] != S[i]))
    
    s.add(Or([S[i] == 1 for i in range(n)]))
    s.add(Or([E[i] == days_total for i in range(n)]))
    
    if s.check() == sat:
        m = s.model()
        intervals = []
        for i in range(n):
            s_val = m.evaluate(S[i]).as_long()
            e_val = m.evaluate(E[i]).as_long()
            intervals.append((s_val, e_val, i))
        
        intervals.sort(key=lambda x: x[0])
        sequence = []
        current_end = -1
        for inter in intervals:
            if inter[0] == 1:
                sequence.append(inter[2])
                current_end = inter[1]
                break
        
        remaining = [inter for inter in intervals if inter[2] not in sequence]
        while remaining:
            found = False
            for inter in remaining:
                if inter[0] == current_end:
                    sequence.append(inter[2])
                    current_end = inter[1]
                    remaining = [r for r in remaining if r[2] != inter[2]]
                    found = True
                    break
            if not found:
                break
        
        print("Travel plan:")
        for idx in sequence:
            s_val = m.evaluate(S[idx]).as_long()
            e_val = m.evaluate(E[idx]).as_long()
            print(f"{cities[idx]}: Days {s_val} to {e_val}")
        
        print("\nFlight days:")
        for i in range(len(sequence) - 1):
            from_city = sequence[i]
            to_city = sequence[i+1]
            flight_day = m.evaluate(E[from_city]).as_long()
            print(f"Day {flight_day}: Fly from {cities[from_city]} to {cities[to_city]}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()