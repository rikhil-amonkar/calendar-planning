from z3 import *

def main():
    s = Solver()
    
    # Given data
    min_start = 2  # First visit starts on day 2 (after 1 travel day from home)
    max_end = 30   # Must return home by day 30
    req_days = [3, 2, 2]  # Days required for City A, B, C
    n_visits = 3  # Total visits
    
    # Arrays for variables
    T = [Int(f'T_{i}') for i in range(n_visits)]  # Start time of each visit
    X = [Int(f'X_{i}') for i in range(n_visits)]  # City visited at each step
    
    # Helper function to get required days for a city symbolically
    def get_req_days(city):
        return If(city == 0, req_days[0],
               If(city == 1, req_days[1],
               req_days[2]))
    
    # Constraints on start times
    for i in range(n_visits):
        # Start time must be at least min_start (2)
        s.add(T[i] >= min_start)
    
    # Order of visits with 1 travel day between
    for i in range(n_visits - 1):
        s.add(T[i+1] == T[i] + get_req_days(X[i]) + 1)
    
    # Each visit must be to a valid city (0, 1, or 2)
    for i in range(n_visits):
        s.add(X[i] >= 0, X[i] <= 2)
    
    # Must visit all three distinct cities
    s.add(Distinct(X))
    
    # Return home must be by day 30
    last_visit_end = T[n_visits-1] + get_req_days(X[n_visits-1]) - 1
    return_day = last_visit_end + 1  # 1 travel day to return home
    s.add(return_day <= max_end)
    
    # Solve the model
    if s.check() == sat:
        m = s.model()
        T_val = [m.evaluate(T[i]).as_long() for i in range(n_visits)]
        X_val = [m.evaluate(X[i]).as_long() for i in range(n_visits)]
        print("Found solution:")
        for i in range(n_visits):
            city = ['A','B','C'][X_val[i]]
            start = T_val[i]
            end = start + req_days[X_val[i]] - 1
            print(f"Visit {i+1}: City {city} from day {start} to {end}")
        
        # Print return travel
        last_end = T_val[-1] + req_days[X_val[-1]] - 1
        print(f"Return home: Day {last_end+1} (arrive home on day {last_end+1})")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()