from z3 import *

def main():
    # Create the solver
    s = Solver()
    
    # Days are 1 to 17
    days = 17
    n = {}  # Naples
    vn = {} # Vienna
    vl = {} # Vilnius
    
    # Initialize variables for each day
    for i in range(1, days + 1):
        n[i] = Bool(f'n_{i}')
        vn[i] = Bool(f'vn_{i}')
        vl[i] = Bool(f'vl_{i}')
    
    # Add constraints for each day
    for i in range(1, days + 1):
        # At least one city per day
        s.add(Or(n[i], vn[i], vl[i]))
        # Cannot be in both Naples and Vilnius on the same day
        s.add(Not(And(n[i], vl[i])))
    
    # Total days in Naples must be 5, and only within days 1-5
    s.add(sum([If(n[i], 1, 0) for i in range(1, days + 1)]) == 5)
    for i in range(6, days + 1):
        s.add(Not(n[i]))
    
    # Total days in Vienna must be 7
    s.add(sum([If(vn[i], 1, 0) for i in range(1, days + 1)]) == 7)
    
    # Total days in Vilnius must be 7
    s.add(sum([If(vl[i], 1, 0) for i in range(1, days + 1)]) == 7)
    
    # Continuity constraint: consecutive days must share at least one city
    for i in range(1, days):
        s.add(Or(
            And(n[i], n[i + 1]),
            And(vn[i], vn[i + 1]),
            And(vl[i], vl[i + 1])
        ))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        # Print the schedule
        for i in range(1, days + 1):
            in_n = m.evaluate(n[i])
            in_vn = m.evaluate(vn[i])
            in_vl = m.evaluate(vl[i])
            
            if in_n == True and in_vn == False and in_vl == False:
                print(f"Day {i}: Naples")
            elif in_n == False and in_vn == True and in_vl == False:
                print(f"Day {i}: Vienna")
            elif in_n == False and in_vn == False and in_vl == True:
                print(f"Day {i}: Vilnius")
            elif in_n == True and in_vn == True and in_vl == False:
                print(f"Day {i}: Travel between Naples and Vienna")
            elif in_n == False and in_vn == True and in_vl == True:
                print(f"Day {i}: Travel between Vienna and Vilnius")
            else:
                # This case should not happen due to constraints
                print(f"Day {i}: Unexpected state")
    else:
        print("No valid schedule found")

if __name__ == "__main__":
    main()