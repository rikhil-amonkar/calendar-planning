from z3 import *

def main():
    # Define the integer variables for the breakpoints a and b
    a = Int('a')
    b = Int('b')
    # Define the city variables: c1, c2, c3 (0: Vilnius, 1: Munich, 2: Mykonos)
    c1 = Int('c1')
    c2 = Int('c2')
    c3 = Int('c3')
    
    s = Solver()
    
    # Allowed direct flight pairs: (Vilnius, Munich), (Munich, Vilnius), (Munich, Mykonos), (Mykonos, Munich)
    allowed_pairs = [(0,1), (1,0), (1,2), (2,1)]
    
    # Constraints for a and b: 1 <= a < b <= 12
    s.add(a >= 1, a <= 11)
    s.add(b >= a+1, b <= 12)
    
    # Constraints for cities: each must be 0, 1, or 2
    s.add(c1 >= 0, c1 <= 2)
    s.add(c2 >= 0, c2 <= 2)
    s.add(c3 >= 0, c3 <= 2)
    
    # Flight constraints between consecutive segments
    s.add(Or([And(c1 == i, c2 == j) for (i, j) in allowed_pairs]))
    s.add(Or([And(c2 == i, c3 == j) for (i, j) in allowed_pairs]))
    
    # Days in each city: 
    days_in_V = If(c1 == 0, a, 0) + If(c2 == 0, (b - a + 1), 0) + If(c3 == 0, (13 - b), 0)
    days_in_M = If(c1 == 1, a, 0) + If(c2 == 1, (b - a + 1), 0) + If(c3 == 1, (13 - b), 0)
    days_in_K = If(c1 == 2, a, 0) + If(c2 == 2, (b - a + 1), 0) + If(c3 == 2, (13 - b), 0)
    
    s.add(days_in_V == 4)
    s.add(days_in_M == 3)
    s.add(days_in_K == 7)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        a_val = m[a].as_long()
        b_val = m[b].as_long()
        c1_val = m[c1].as_long()
        c2_val = m[c2].as_long()
        c3_val = m[c3].as_long()
        
        city_names = {0: 'Vilnius', 1: 'Munich', 2: 'Mykonos'}
        
        print(f"Stay in {city_names[c1_val]} from day 1 to day {a_val}.")
        print(f"Stay in {city_names[c2_val]} from day {a_val} to day {b_val}.")
        print(f"Stay in {city_names[c3_val]} from day {b_val} to day 12.")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()