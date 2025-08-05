from z3 import *

def main():
    cities = ['Tallinn', 'Helsinki', 'Budapest', 'Geneva', 'Porto', 'Edinburgh', 'Riga', 'Vilnius', 'Oslo']
    n = len(cities)
    
    # Travel time matrix
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
    
    # Decision variables
    seq = [Int(f'seq_{i}') for i in range(n)]  # Visit sequence
    s = [Int(f's_{i}') for i in range(n)]      # Start day for each city
    d = [Int(f'd_{i}') for i in range(n)]      # Stay duration for each city
    
    # Fixed start and end cities
    solver.add(seq[0] == 0)  # Start with Tallinn
    solver.add(seq[n-1] == 8)  # End with Oslo
    
    # Valid city indices and distinct sequence
    for i in range(n):
        solver.add(seq[i] >= 0, seq[i] < n)
    solver.add(Distinct(seq))
    
    # Minimum stay of 2 days for all cities
    for i in range(n):
        solver.add(d[i] >= 2)
        solver.add(s[i] >= 1)
    
    # Start in Tallinn on day 1
    solver.add(s[0] == 1)
    
    # End in Oslo exactly on day 25
    solver.add(s[n-1] + d[n-1] - 1 == 25)
    
    # Travel time helper function
    def travel_time(from_city, to_city):
        expr = IntVal(T[0][0])
        for i in range(n):
            for j in range(n):
                expr = If(And(from_city == i, to_city == j), T[i][j], expr)
        return expr
    
    # Correct timeline chaining
    for i in range(n-1):
        from_city = seq[i]
        to_city = seq[i+1]
        tt = travel_time(from_city, to_city)
        solver.add(s[i+1] == s[i] + d[i] - 1 + tt)
    
    # Solve and output results
    if solver.check() == sat:
        model = solver.model()
        seq_val = [model.evaluate(seq[i]).as_long() for i in range(n)]
        s_val = [model.evaluate(s[i]).as_long() for i in range(n)]
        d_val = [model.evaluate(d[i]).as_long() for i in range(n)]
        
        itinerary = []
        for i in range(n):
            start = s_val[i]
            end = start + d_val[i] - 1
            day_range = f"Day {start}-{end}" if start != end else f"Day {start}"
            itinerary.append({
                'day_range': day_range,
                'place': cities[seq_val[i]]
            })
        
        print("Plan found:", {'itinerary': itinerary})
    else:
        print("No valid plan found")

if __name__ == '__main__':
    main()