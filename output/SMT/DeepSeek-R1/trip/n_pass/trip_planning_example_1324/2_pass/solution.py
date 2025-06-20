from z3 import *
import json

def main():
    cities = ["Venice", "Barcelona", "Copenhagen", "Lyon", "Reykjavik", "Dubrovnik", "Athens", "Tallinn", "Munich"]
    durs = [4, 3, 4, 4, 4, 5, 2, 5, 3]
    n = len(cities)
    
    flight_list = [
        ('Copenhagen', 'Athens'),
        ('Copenhagen', 'Dubrovnik'),
        ('Munich', 'Tallinn'),
        ('Copenhagen', 'Munich'),
        ('Venice', 'Munich'),
        ('Reykjavik', 'Athens'),
        ('Athens', 'Dubrovnik'),
        ('Venice', 'Athens'),
        ('Lyon', 'Barcelona'),
        ('Copenhagen', 'Reykjavik'),
        ('Reykjavik', 'Munich'),
        ('Athens', 'Munich'),
        ('Lyon', 'Munich'),
        ('Barcelona', 'Reykjavik'),
        ('Venice', 'Copenhagen'),
        ('Barcelona', 'Dubrovnik'),
        ('Lyon', 'Venice'),
        ('Dubrovnik', 'Munich'),
        ('Barcelona', 'Athens'),
        ('Copenhagen', 'Barcelona'),
        ('Venice', 'Barcelona'),
        ('Barcelona', 'Munich'),
        ('Barcelona', 'Tallinn'),
        ('Copenhagen', 'Tallinn')
    ]
    
    allowed = [[0]*n for _ in range(n)]
    for city1, city2 in flight_list:
        idx1 = cities.index(city1)
        idx2 = cities.index(city2)
        allowed[idx1][idx2] = 1
        allowed[idx2][idx1] = 1
    
    allowed_pairs = []
    for j in range(n):
        for k in range(n):
            if allowed[j][k] == 1:
                allowed_pairs.append((j, k))
    
    s = Solver()
    
    assign = [[Bool('a_%d_%d' % (i, j)) for j in range(n)] for i in range(n)]
    
    for i in range(n):
        s.add(Or([assign[i][j] for j in range(n)]))
        s.add(Sum([If(assign[i][j], 1, 0) for j in range(n)]) == 1)
    
    for j in range(n):
        s.add(Sum([If(assign[i][j], 1, 0) for i in range(n)]) == 1)
    
    prefix = [Int('prefix_%d' % i) for i in range(n)]
    s.add(prefix[0] == 0)
    for i in range(1, n):
        sum_dur = Sum([If(assign[i-1][j], durs[j], 0) for j in range(n)])
        s.add(prefix[i] == prefix[i-1] + sum_dur - 1)
    
    S_bcn = Int('S_bcn')
    s.add(S_bcn == 1 + Sum([If(assign[i][1], prefix[i], 0) for i in range(n)]))
    E_bcn = S_bcn + durs[1] - 1
    s.add(S_bcn <= 12)
    s.add(E_bcn >= 10)
    
    S_cop = Int('S_cop')
    s.add(S_cop == 1 + Sum([If(assign[i][2], prefix[i], 0) for i in range(n)]))
    E_cop = S_cop + durs[2] - 1
    s.add(S_cop <= 10)
    s.add(E_cop >= 7)
    
    S_dub = Int('S_dub')
    s.add(S_dub == 1 + Sum([If(assign[i][5], prefix[i], 0) for i in range(n)]))
    s.add(assign[5][5])  # Dubrovnik at position 5
    for i in range(5):
        s.add(Not(assign[i][5]))
    s.add(prefix[5] == 15)
    
    for i in range(n-1):
        or_terms = []
        for j, k in allowed_pairs:
            or_terms.append(And(assign[i][j], assign[i+1][k]))
        s.add(Or(or_terms))
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(n):
            j_index = None
            for j in range(n):
                if model.evaluate(assign[i][j]):
                    j_index = j
                    break
            if j_index is None:
                continue
            city_name = cities[j_index]
            prefix_val = model.evaluate(prefix[i])
            if isinstance(prefix_val, IntNumRef):
                prefix_val = prefix_val.as_long()
            start = prefix_val + 1
            duration = durs[j_index]
            end = start + duration - 1
            if start == end:
                day_range_str = f"Day {start}"
            else:
                day_range_str = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range_str, "place": city_name})
            if i < n-1:
                itinerary.append({"day_range": f"Day {end}", "place": city_name})
                j_next = None
                for j in range(n):
                    if model.evaluate(assign[i+1][j]):
                        j_next = j
                        break
                if j_next is not None:
                    next_city = cities[j_next]
                    itinerary.append({"day_range": f"Day {end}", "place": next_city})
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()