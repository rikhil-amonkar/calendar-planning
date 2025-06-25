from z3 import *
import json

def main():
    cities = ['Riga', 'Manchester', 'Bucharest', 'Florence', 'Vienna', 'Istanbul', 'Reykjavik', 'Stuttgart']
    n_days = 23
    n_cities = len(cities)
    city_index = {city: idx for idx, city in enumerate(cities)}
    req = [4, 5, 4, 4, 2, 2, 4, 5]

    directed_edges = []
    bidirectional = [
        ('Bucharest', 'Vienna'),
        ('Reykjavik', 'Vienna'),
        ('Manchester', 'Vienna'),
        ('Manchester', 'Riga'),
        ('Riga', 'Vienna'),
        ('Istanbul', 'Vienna'),
        ('Vienna', 'Florence'),
        ('Stuttgart', 'Vienna'),
        ('Riga', 'Bucharest'),
        ('Istanbul', 'Riga'),
        ('Stuttgart', 'Istanbul'),
        ('Istanbul', 'Bucharest'),
        ('Manchester', 'Istanbul'),
        ('Manchester', 'Bucharest'),
        ('Stuttgart', 'Manchester')
    ]
    for (a, b) in bidirectional:
        i = city_index[a]
        j = city_index[b]
        directed_edges.append((i, j))
        directed_edges.append((j, i))
    directed_edges.append((city_index['Reykjavik'], city_index['Stuttgart']))

    X = [[Bool(f'x_{d}_{c}') for c in range(n_cities)] for d in range(n_days)]
    s = Solver()

    for c in range(n_cities):
        total = Sum([If(X[d][c], 1, 0) for d in range(n_days)])
        s.add(total == req[c])

    for d in range(n_days):
        if d == 11 or d == 12:
            s.add(X[d][city_index['Istanbul']] == True)
        else:
            s.add(X[d][city_index['Istanbul']] == False)

    for d in range(n_days):
        if d in [15, 16, 17, 18]:
            s.add(X[d][city_index['Bucharest']] == True)
        else:
            s.add(X[d][city_index['Bucharest']] == False)

    Y = [Int(f'Y_{d}') for d in range(n_days)]
    for d in range(n_days):
        s.add(Y[d] == Sum([If(X[d][c], 1, 0) for c in range(n_cities)]))
        if d in [11, 12, 15, 18]:
            s.add(Y[d] == 2)
        elif d in [16, 17]:
            s.add(Y[d] == 1)
        else:
            s.add(Or(Y[d] == 1, Y[d] == 2))
    s.add(Sum([Y[d] - 1 for d in range(n_days)]) == 7)

    for d in range(n_days - 1):
        s.add(Or([And(X[d][c], X[d+1][c]) for c in range(n_cities)]))

    for d in range(1, n_days - 1):
        common_prev = [And(X[d-1][c], X[d][c]) for c in range(n_cities)]
        common_next = [And(X[d][c], X[d+1][c]) for c in range(n_cities)]
        s.add(Implies(Y[d] == 2, Sum([If(common_prev[c], 1, 0) for c in range(n_cities)]) == 1))
        s.add(Implies(Y[d] == 2, Sum([If(common_next[c], 1, 0) for c in range(n_cities)]) == 1))
        dep = Int(f'dep_{d}')
        arr = Int(f'arr_{d}')
        s.add(Implies(Y[d] == 2, Or([And(dep == c, common_prev[c]) for c in range(n_cities)])))
        s.add(Implies(Y[d] == 2, Or([And(arr == c, common_next[c]) for c in range(n_cities)])))
        s.add(Implies(Y[d] == 2, dep != arr))
        edge_constraint = Or([And(dep == i, arr == j) for (i, j) in directed_edges])
        s.add(Implies(Y[d] == 2, edge_constraint))

    if s.check() == sat:
        model = s.model()
        travel_days = []
        for d in range(n_days):
            if model[Y[d]].as_long() == 2:
                travel_days.append(d)
        
        records = []
        for c in range(n_cities):
            days_c = []
            for d in range(n_days):
                if is_true(model[X[d][c]]):
                    days_c.append(d)
            if not days_c:
                continue
            days_c.sort()
            segments = []
            start = days_c[0]
            end = start
            for i in range(1, len(days_c)):
                if days_c[i] == end + 1:
                    end = days_c[i]
                else:
                    segments.append((start, end))
                    start = days_c[i]
                    end = start
            segments.append((start, end))
            
            for seg in segments:
                start_d, end_d = seg
                if start_d == end_d:
                    day_str = f"Day {start_d + 1}"
                else:
                    day_str = f"Day {start_d + 1}-{end_d + 1}"
                records.append((start_d, 'segment', day_str, cities[c]))
            
            for d in travel_days:
                if d in days_c:
                    day_str = f"Day {d + 1}"
                    records.append((d, 'travel', day_str, cities[c]))
        
        records.sort(key=lambda x: (x[0], 0 if x[1] == 'segment' else 1))
        itinerary_list = [{"day_range": day_str, "place": city} for (_, _, day_str, city) in records]
        result = {"itinerary": itinerary_list}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()