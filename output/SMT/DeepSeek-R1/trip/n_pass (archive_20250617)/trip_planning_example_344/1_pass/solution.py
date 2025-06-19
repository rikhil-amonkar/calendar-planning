from z3 import *

def main():
    # City representations
    Valencia = 0
    Athens = 1
    Naples = 2
    Zurich = 3
    city_names = {
        Valencia: 'Valencia',
        Athens: 'Athens',
        Naples: 'Naples',
        Zurich: 'Zurich'
    }
    
    # L[0] to L[20]: L[0] is the start of day1, L[1] to L[20] are the end of days 1 to 20.
    L = [Int(f'L_{i}') for i in range(21)]
    
    s = Solver()
    
    # Constraint: Start in Athens at the beginning of day 1
    s.add(L[0] == Athens)
    
    # Days 1-6: Must be in Athens each day
    for d in range(1, 7):
        s.add(Or(L[d-1] == Athens, L[d] == Athens))
    
    # Days 16-20: Must be in Naples each day
    for d in range(16, 21):
        s.add(Or(L[d-1] == Naples, L[d] == Naples))
    
    # Days 7-15: Must not be in Athens
    for d in range(7, 16):
        s.add(And(L[d-1] != Athens, L[d] != Athens))
    
    # Days 1-15: Must not be in Naples
    for d in range(1, 16):
        s.add(And(L[d-1] != Naples, L[d] != Naples))
    
    # Count days in Valencia and Zurich
    valencia_days = 0
    zurich_days = 0
    for d in range(1, 21):
        in_valencia = Or(L[d-1] == Valencia, L[d] == Valencia)
        in_zurich = Or(L[d-1] == Zurich, L[d] == Zurich)
        valencia_days += If(in_valencia, 1, 0)
        zurich_days += If(in_zurich, 1, 0)
    s.add(valencia_days == 6)
    s.add(zurich_days == 6)
    
    # Exactly one travel day in days 7-15
    travel_days_mid = 0
    for d in range(7, 16):
        travel_days_mid += If(L[d-1] != L[d], 1, 0)
    s.add(travel_days_mid == 1)
    
    # In the period from day6 to day15, we are only in Valencia or Zurich
    for d in range(6, 16):
        s.add(Or(L[d] == Valencia, L[d] == Zurich))
    
    # Each location variable must be one of the four cities
    for i in range(1, 21):
        s.add(Or(L[i] == Valencia, L[i] == Athens, L[i] == Naples, L[i] == Zurich))
    
    # Check and get the model
    if s.check() == sat:
        m = s.model()
        res = [m.evaluate(L[i]).as_long() for i in range(21)]
        
        # Output the plan
        for d in range(1, 21):
            start_city = res[d-1]
            end_city = res[d]
            if start_city == end_city:
                print(f"Day {d}: {city_names[start_city]}")
            else:
                print(f"Day {d}: {city_names[start_city]} and {city_names[end_city]}")
    else:
        print("No valid plan found.")

if __name__ == "__main__":
    main()