from z3 import *

def main():
    # Create integer variables for the cities and travel days
    A = Int('A')
    B = Int('B')
    C = Int('C')
    t = Int('t')
    s = Int('s')
    
    solver = Solver()
    
    # Cities: 0 = Bucharest, 1 = Lyon, 2 = Porto
    cities = [0, 1, 2]
    
    # Constraints for A, B, C: distinct and in {0,1,2}
    solver.add(Distinct(A, B, C))
    solver.add(A >= 0, A <= 2)
    solver.add(B >= 0, B <= 2)
    solver.add(C >= 0, C <= 2)
    
    # Direct flight constraints: only Bucharest<->Lyon and Lyon<->Porto
    # Flight from A to B must be direct
    solver.add(Or(
        And(A == 0, B == 1),
        And(A == 1, B == 0),
        And(A == 1, B == 2),
        And(A == 2, B == 1)
    ))
    # Flight from B to C must be direct
    solver.add(Or(
        And(B == 0, C == 1),
        And(B == 1, C == 0),
        And(B == 1, C == 2),
        And(B == 2, C == 1)
    ))
    
    # Constraints for t and s: 1 <= t < s <= 16
    solver.add(t >= 1)
    solver.add(t <= 15)  # since s must be at least t+1 and <=16
    solver.add(s >= t + 1)
    solver.add(s <= 16)
    
    # Define the days spent in each city
    days0 = If(A == 0, t, If(B == 0, s - t + 1, If(C == 0, 16 - s + 1, 0)))
    days1 = If(A == 1, t, If(B == 1, s - t + 1, If(C == 1, 16 - s + 1, 0)))
    days2 = If(A == 2, t, If(B == 2, s - t + 1, If(C == 2, 16 - s + 1, 0)))
    
    # Days constraints: Bucharest=7, Lyon=7, Porto=4
    solver.add(days0 == 7)
    solver.add(days1 == 7)
    solver.add(days2 == 4)
    
    # Wedding constraint: must be in Bucharest (city0) on at least one day between 1 and 7
    solver.add(Or(
        And(A == 0),  # Bucharest is first city: always covers day 1
        And(B == 0, t <= 7),  # Bucharest is second city: must arrive by day 7
        And(C == 0, s <= 7)   # Bucharest is third city: must arrive by day 7
    ))
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        A_val = model[A].as_long()
        B_val = model[B].as_long()
        C_val = model[C].as_long()
        t_val = model[t].as_long()
        s_val = model[s].as_long()
        
        city_names = {0: 'Bucharest', 1: 'Lyon', 2: 'Porto'}
        
        print(f"Days 1 to {t_val}: stay in {city_names[A_val]}")
        print(f"Days {t_val} to {s_val}: stay in {city_names[B_val]}")
        print(f"Days {s_val} to 16: stay in {city_names[C_val]}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()