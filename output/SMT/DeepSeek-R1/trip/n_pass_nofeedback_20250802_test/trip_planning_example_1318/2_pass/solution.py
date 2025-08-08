from z3 import *

def main():
    cities = ['Tallinn', 'Helsinki', 'Budapest', 'Geneva', 'Porto', 'Edinburgh', 'Riga', 'Vilnius', 'Oslo']
    n = len(cities)
    
    T = [
        [0, 1, 3, 3, 4, 4, 1, 2, 3],
        [1, 0, 3, 3, 4, 4, 1, 2, 3],
        [3, 3, 0, 2, 4, 3, 3, 3, 3],
        [3, 3, 2, 0, 2, 2, 3, 3, 2],
        [4, 4, 4, 2, 0, 3, 4, 4, 3],
        [4, 4, 3, 2, 3, 0, 4, 4, 2],
        [1, 1, 3, 3, 4, 4, 0, 1, 2],
        [2, 2, 3, 3, 4, 4, 1, 0, 2],
        [3, 3, 3, 2, 3, 2, 2, 2, 0]
    ]
    
    solver = Solver()
    
    seq = [Int(f'seq_{i}') for i in range(n)]
    s = [Int(f's_{i}') for i in range(n)]
    d = [Int(f'd_{i}') for i in range(n)]
    
    solver.add(seq[0] == 0)
    solver.add(seq[n-1] == 8)
    solver.add(Distinct(seq))
    for i in range(n):
        solver.add(seq[i] >= 0, seq[i] < n)
    
    solver.add(s[0] == 1)
    for i in range(n-1):
        solver.add(d[i] >= 2)
    solver.add(d[n-1] == 26 - s[n-1])
    solver.add(s[n-1] >= 1, s[n-1] <= 25)
    solver.add(d[n-1] >= 1)
    
    T_z3 = Array('T', IntSort(), ArraySort(IntSort(), IntSort()))
    for i in range(n):
        row = Array(f'row_{i}', IntSort(), IntSort())
        for j in range(n):
            row = Store(row, j, T[i][j])
        T_z3 = Store(T_z3, i, row)
    
    for i in range(n-1):
        from_city = seq[i]
        to_city = seq[i+1]
        travel_time = Select(Select(T_z3, from_city), to_city)
        solver.add(s[i+1] == s[i] + d[i] + travel_time)
    
    if solver.check() == sat:
        model = solver.model()
        seq_val = [model.evaluate(seq[i]).as_long() for i in range(n)]
        s_val = [model.evaluate(s[i]).as_long() for i in range(n)]
        d_val = [model.evaluate(d[i]).as_long() for i in range(n)]
        
        itinerary = []
        for i in range(n):
            start = s_val[i]
            end = start + d_val[i] - 1
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            itinerary.append({
                'day_range': day_range,
                'place': cities[seq_val[i]]
            })
        
        plan = {'itinerary': itinerary}
        print("Plan found:", plan)
    else:
        print("No valid plan found")

if __name__ == '__main__':
    main()