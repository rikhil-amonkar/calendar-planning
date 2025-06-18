from z3 import *

def main():
    s = Solver()
    n_days = 11
    city_names = {0: 'Krakow', 1: 'Paris', 2: 'Seville'}
    allowed_pairs = [(0, 1), (1, 0), (1, 2), (2, 1)]
    
    # City at start of each day (days 1-11) and end of day 11
    city = [Int(f'city_{i}') for i in range(n_days + 1)]
    for i in range(n_days + 1):
        s.add(Or(city[i] == 0, city[i] == 1, city[i] == 2))
    
    # Travel occurs when consecutive cities differ
    travel = [Bool(f'travel_{i}') for i in range(1, n_days + 1)]
    for i in range(1, n_days + 1):
        s.add(travel[i-1] == (city[i-1] != city[i]))
        s.add(Implies(travel[i-1], 
                      Or([And(city[i-1] == a, city[i] == b) for (a, b) in allowed_pairs])))
    
    # Track presence in each city per calendar day
    inK = [Bool(f'inK_{i}') for i in range(n_days)]
    inP = [Bool(f'inP_{i}') for i in range(n_days)]
    inS = [Bool(f'inS_{i}') for i in range(n_days)]
    
    for i in range(n_days):
        # Present in city if at start or end of day
        s.add(inK[i] == Or(city[i] == 0, city[i+1] == 0))
        s.add(inP[i] == Or(city[i] == 1, city[i+1] == 1))
        s.add(inS[i] == Or(city[i] == 2, city[i+1] == 2))
    
    # City-day totals
    totalK = Sum([If(inK[i], 1, 0) for i in range(n_days)])
    totalP = Sum([If(inP[i], 1, 0) for i in range(n_days)])
    totalS = Sum([If(inS[i], 1, 0) for i in range(n_days)])
    s.add(totalK == 5, totalP == 2, totalS == 6)
    
    # Workshop constraint: full day in Krakow (no travel) during days 1-5
    s.add(Or([And(city[i] == 0, city[i+1] == 0) for i in range(5)]))
    
    # Exactly 2 travel days
    total_travel = Sum([If(travel[i], 1, 0) for i in range(n_days)])
    s.add(total_travel == 2)
    
    if s.check() == sat:
        m = s.model()
        city_vals = [m.evaluate(city[i]) for i in range(n_days + 1)]
        travel_vals = [m.evaluate(travel[i]) for i in range(n_days)]
        
        for day in range(1, n_days + 1):
            idx = day - 1
            if travel_vals[idx]:
                from_city = city_vals[idx].as_long()
                to_city = city_vals[idx + 1].as_long()
                print(f"Day {day}: Travel from {city_names[from_city]} to {city_names[to_city]} (present in both)")
            else:
                city_val = city_vals[idx].as_long()
                print(f"Day {day}: Stay in {city_names[city_val]}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()