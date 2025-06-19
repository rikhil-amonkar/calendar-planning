from z3 import *

def main():
    cities = ['Mykonos', 'Nice', 'Prague', 'Bucharest', 'Zurich', 'Valencia', 'Riga']
    days_list = [3, 2, 3, 5, 5, 5, 5]
    city_to_index = {city: idx for idx, city in enumerate(cities)}
    
    edges = [
        ('Mykonos', 'Nice'), ('Mykonos', 'Zurich'),
        ('Prague', 'Bucharest'), ('Valencia', 'Bucharest'),
        ('Zurich', 'Prague'), ('Riga', 'Nice'),
        ('Zurich', 'Riga'), ('Zurich', 'Bucharest'),
        ('Zurich', 'Valencia'), ('Bucharest', 'Riga'),
        ('Prague', 'Riga'), ('Prague', 'Valencia'),
        ('Zurich', 'Nice')
    ]
    directed_edges = []
    for a, b in edges:
        idx_a = city_to_index[a]
        idx_b = city_to_index[b]
        directed_edges.append((idx_a, idx_b))
        directed_edges.append((idx_b, idx_a))
    
    c1, c2, c3, c4, c5, c6, c7 = Ints('c1 c2 c3 c4 c5 c6 c7')
    s = Solver()
    
    for ci in [c1, c2, c3, c4, c5, c6, c7]:
        s.add(ci >= 0, ci < 7)
    s.add(Distinct(c1, c2, c3, c4, c5, c6, c7))
    
    for i in range(6):
        curr = [c1, c2, c3, c4, c5, c6, c7][i]
        nxt = [c1, c2, c3, c4, c5, c6, c7][i+1]
        s.add(Or([And(curr == a, nxt == b) for (a, b) in directed_edges]))
    
    def day_func(c):
        return If(c == 0, 3,
              If(c == 1, 2,
              If(c == 2, 3,
              If(c == 3, 5,
              If(c == 4, 5,
              If(c == 5, 5, 5))))))
    
    d1 = day_func(c1)
    d2 = day_func(c2)
    d3 = day_func(c3)
    d4 = day_func(c4)
    d5 = day_func(c5)
    d6 = day_func(c6)
    d7 = day_func(c7)
    
    S0 = 0
    S1 = Int('S1')
    S2 = Int('S2')
    S3 = Int('S3')
    S4 = Int('S4')
    S5 = Int('S5')
    S6 = Int('S6')
    S7 = Int('S7')
    s.add(S1 == S0 + d1)
    s.add(S2 == S1 + d2)
    s.add(S3 == S2 + d3)
    s.add(S4 == S3 + d4)
    s.add(S5 == S4 + d5)
    s.add(S6 == S5 + d6)
    s.add(S7 == S6 + d7)
    
    S = [S0, S1, S2, S3, S4, S5, S6, S7]
    positions = [c1, c2, c3, c4, c5, c6, c7]
    
    mykonos_index = city_to_index['Mykonos']
    prague_index = city_to_index['Prague']
    
    for j in range(7):
        s.add(Implies(positions[j] == mykonos_index, S[j] - j <= 2))
    
    for j in range(7):
        s.add(Implies(positions[j] == prague_index, 
                      And(S[j] - j >= 4, S[j] - j <= 8)))
    
    if s.check() == sat:
        m = s.model()
        order = [m.evaluate(c1), m.evaluate(c2), m.evaluate(c3), 
                 m.evaluate(c4), m.evaluate(c5), m.evaluate(c6), m.evaluate(c7)]
        city_names = []
        for idx in order:
            city_names.append(cities[idx.as_long()])
        
        cum = 0
        segments = []
        for i in range(7):
            city_idx = order[i].as_long()
            d = days_list[city_idx]
            start_day = 1 + cum - i
            end_day = start_day + d - 1
            segments.append((start_day, end_day, cities[city_idx]))
            cum += d
        
        itinerary = []
        for i in range(len(segments)):
            start, end, city = segments[i]
            itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
            if i < len(segments) - 1:
                itinerary.append({"day_range": f"Day {end}", "place": city})
                next_city = segments[i+1][2]
                itinerary.append({"day_range": f"Day {end}", "place": next_city})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()