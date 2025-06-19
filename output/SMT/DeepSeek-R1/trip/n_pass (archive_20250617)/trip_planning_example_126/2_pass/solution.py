from z3 import *

def main():
    s = Solver()
    n_days = 11
    city_names = {0: 'Krakow', 1: 'Paris', 2: 'Seville'}
    allowed_pairs = [(0, 1), (1, 0), (1, 2), (2, 1)]
    
    start_city = [Int(f'start_city_{i}') for i in range(n_days + 1)]
    for i in range(n_days + 1):
        s.add(Or(start_city[i] == 0, start_city[i] == 1, start_city[i] == 2))
    
    travel = [Bool(f'travel_{i}') for i in range(1, n_days + 1)]
    
    for i in range(1, n_days + 1):
        s.add(If(travel[i-1],
                 Or([And(start_city[i-1] == a, start_city[i] == b) for (a, b) in allowed_pairs]),
                 start_city[i] == start_city[i-1]))
    
    inK = [Bool(f'inK_{i}') for i in range(1, n_days + 1)]
    inP = [Bool(f'inP_{i}') for i in range(1, n_days + 1)]
    inS = [Bool(f'inS_{i}') for i in range(1, n_days + 1)]
    
    for i in range(1, n_days + 1):
        s.add(inK[i-1] == Or(start_city[i-1] == 0, start_city[i] == 0))
        s.add(inP[i-1] == Or(start_city[i-1] == 1, start_city[i] == 1))
        s.add(inS[i-1] == Or(start_city[i-1] == 2, start_city[i] == 2))
    
    totalK = Sum([If(inK[i], 1, 0) for i in range(n_days)])
    totalP = Sum([If(inP[i], 1, 0) for i in range(n_days)])
    totalS = Sum([If(inS[i], 1, 0) for i in range(n_days)])
    s.add(totalK == 5, totalP == 2, totalS == 6)
    
    s.add(Or([And(inK[i], Not(travel[i])) for i in range(5)]))
    
    total_travel = Sum([If(travel[i], 1, 0) for i in range(n_days)])
    s.add(total_travel == 2)
    
    if s.check() == sat:
        m = s.model()
        start_city_vals = [m.evaluate(start_city[i]) for i in range(n_days + 1)]
        travel_vals = [m.evaluate(travel[i]) for i in range(n_days)]
        
        for day in range(1, n_days + 1):
            idx = day - 1
            if travel_vals[idx]:
                from_city = start_city_vals[idx].as_long()
                to_city = start_city_vals[idx + 1].as_long()
                print(f"Day {day}: Travel from {city_names[from_city]} to {city_names[to_city]} (present in both)")
            else:
                city = start_city_vals[idx].as_long()
                print(f"Day {day}: Stay in {city_names[city]}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()