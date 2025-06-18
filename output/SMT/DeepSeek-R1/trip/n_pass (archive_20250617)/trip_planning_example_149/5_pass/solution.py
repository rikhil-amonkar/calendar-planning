from z3 import *

def main():
    # Cities: 0=Istanbul, 1=London, 2=Santorini
    s = [Int('s_%d' % i) for i in range(10)]  # s[0] to s[9] for days 1 to 10
    t = [Bool('t_%d' % i) for i in range(10)]  # t[i] is True if travel on day i+1
    
    solver = Solver()
    
    # Allowed direct flights: Istanbul<->London, London<->Santorini
    allowed_pairs = [(0, 1), (1, 0), (1, 2), (2, 1)]
    
    # Travel constraints for days 1-9
    for i in range(9):
        # If traveling, must be allowed flight between current and next city
        solver.add(Implies(t[i], Or([And(s[i] == a, s[i+1] == b) for (a, b) in allowed_pairs)))
        # If not traveling, stay in same city
        solver.add(Implies(Not(t[i]), s[i] == s[i+1]))
    
    # Cannot travel on day 10 (no next day)
    solver.add(Not(t[9]))
    
    # Start in Istanbul on day 1
    solver.add(s[0] == 0)
    
    # Must be in Santorini on day 5 and day 10
    solver.add(Or(s[4] == 2, And(t[4], s[5] == 2)))  # Day 5
    solver.add(s[9] == 2)  # Day 10
    
    # Count days in each city (including travel days)
    count_ist, count_lon, count_san = 0, 0, 0
    for i in range(10):
        # Count starting city for the day
        count_ist += If(s[i] == 0, 1, 0)
        count_lon += If(s[i] == 1, 1, 0)
        count_san += If(s[i] == 2, 1, 0)
        
        # If traveling, also count destination city
        if i < 9:  # Only days 1-9 can have travel
            count_ist += If(And(t[i], s[i+1] == 0), 1, 0)
            count_lon += If(And(t[i], s[i+1] == 1), 1, 0)
            count_san += If(And(t[i], s[i+1] == 2), 1, 0)
    
    # Apply city day constraints
    solver.add(count_ist == 3, count_lon == 3, count_san == 6)
    
    # Exactly 2 travel days (can only happen on days 1-9)
    solver.add(Sum([If(t_i, 1, 0) for t_i in t[:9]]) == 2)
    
    # Cities must be valid (0, 1, or 2)
    for i in range(10):
        solver.add(Or(s[i] == 0, s[i] == 1, s[i] == 2))
    
    # Solve and print itinerary
    if solver.check() == sat:
        m = solver.model()
        s_val = [m.evaluate(s_i) for s_i in s]
        t_val = [m.evaluate(t_i) for t_i in t]
        
        cities = ["Istanbul", "London", "Santorini"]
        for day in range(10):
            city_idx = s_val[day].as_long()
            city = cities[city_idx]
            if t_val[day].as_bool() and day < 9:  # Travel day
                next_city = cities[s_val[day+1].as_long()]
                print(f"Day {day+1}: Start in {city}, fly to {next_city} -> in {city} and {next_city}")
            else:  # Stay day
                print(f"Day {day+1}: Stay in {city}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()