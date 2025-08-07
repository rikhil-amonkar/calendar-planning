from z3 import *
import json

def main():
    # City mapping
    cities = ["Riga", "Frankfurt", "Amsterdam", "Vilnius", "London", "Stockholm", "Bucharest"]
    # Required days per city: [Riga, Frankfurt, Amsterdam, Vilnius, London, Stockholm, Bucharest]
    required_days = [2, 3, 2, 5, 2, 3, 4]
    
    # Directed flight edges: (from, to)
    directed_edges = [
        (4, 2), (2, 4),  # London <-> Amsterdam
        (3, 1), (1, 3),  # Vilnius <-> Frankfurt
        (0, 3),           # Riga -> Vilnius (only)
        (0, 5), (5, 0),   # Riga <-> Stockholm
        (4, 6), (6, 4),   # London <-> Bucharest
        (2, 5), (5, 2),   # Amsterdam <-> Stockholm
        (2, 1), (1, 2),   # Amsterdam <-> Frankfurt
        (1, 5), (5, 1),   # Frankfurt <-> Stockholm
        (6, 0), (0, 6),   # Bucharest <-> Riga
        (2, 0), (0, 2),   # Amsterdam <-> Riga
        (2, 6), (6, 2),   # Amsterdam <-> Bucharest
        (0, 1), (1, 0),   # Riga <-> Frankfurt
        (6, 1), (1, 6),   # Bucharest <-> Frankfurt
        (4, 1), (1, 4),   # London <-> Frankfurt
        (4, 5), (5, 4),   # London <-> Stockholm
        (2, 3), (3, 2)    # Amsterdam <-> Vilnius
    ]
    
    # Create Z3 variables for each day (s0 to s14)
    s = [Int('s_%d' % i) for i in range(15)]
    
    solver = Solver()
    
    # Each day variable must be between 0 and 6 (inclusive)
    for i in range(15):
        solver.add(s[i] >= 0, s[i] <= 6)
    
    # Flight constraints for consecutive days
    for i in range(14):  # i from 0 to 13 (for days 1-14)
        # If moving to a different city, ensure a direct flight exists
        move_cond = s[i] != s[i+1]
        flight_ok = Or([And(s[i] == u, s[i+1] == v) for (u, v) in directed_edges])
        solver.add(Implies(move_cond, flight_ok))
    
    # Total days per city
    for c in range(7):
        total = 0
        # For days 1 to 14 (i from 0 to 13)
        for i in range(0, 14):
            cond = Or(s[i] == c, And(s[i] != s[i+1], s[i+1] == c))
            total += If(cond, 1, 0)
        # Day 15
        total += If(s[14] == c, 1, 0)
        solver.add(total == required_days[c])
    
    # Event in Amsterdam: must be present on day 2 or 3
    cond_day2 = Or(s[1] == 2, And(s[1] != s[2], s[2] == 2))
    cond_day3 = Or(s[2] == 2, And(s[2] != s[3], s[3] == 2))
    solver.add(Or(cond_day2, cond_day3))
    
    # Event in Vilnius: must be present on at least one day between 7 and 11 (inclusive)
    conds_vilnius = []
    for i in [6, 7, 8, 9, 10]:  # indices for days 7 to 11
        cond = Or(s[i] == 3, And(s[i] != s[i+1], s[i+1] == 3))
        conds_vilnius.append(cond)
    solver.add(Or(conds_vilnius))
    
    # Event in Stockholm: must be present on at least one day between 13 and 15 (inclusive)
    cond_day13 = Or(s[12] == 5, And(s[12] != s[13], s[13] == 5))
    cond_day14 = Or(s[13] == 5, And(s[13] != s[14], s[14] == 5))
    cond_day15 = (s[14] == 5)
    solver.add(Or(cond_day13, cond_day14, cond_day15))
    
    # Solve the problem
    if solver.check() == sat:
        m = solver.model()
        s_val = [m.evaluate(s[i]).as_long() for i in range(15)]
        
        itinerary = []
        for day in range(1, 16):
            idx = day - 1
            if day < 15:
                if s_val[idx] != s_val[idx+1]:
                    place = cities[s_val[idx]] + ", " + cities[s_val[idx+1]]
                else:
                    place = cities[s_val[idx]]
            else:
                place = cities[s_val[14]]
            itinerary.append({"day": day, "place": place})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()