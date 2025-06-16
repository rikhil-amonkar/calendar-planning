from z3 import *

def main():
    s = Solver()
    cities = ['Bucharest', 'Warsaw', 'Stuttgart', 'Copenhagen', 'Dubrovnik']
    n_days = 19
    n_travel_days = n_days - 1
    city = [Int('city_%d' % i) for i in range(n_days)]
    travel = [Bool('travel_%d' % i) for i in range(n_travel_days)]
    
    for i in range(n_days):
        s.add(city[i] >= 0, city[i] <= 4)
    
    allowed_edges = [
        (1, 3), (3, 1),
        (2, 3), (3, 2),
        (1, 2), (2, 1),
        (0, 3), (3, 0),
        (0, 1), (1, 0),
        (3, 4), (4, 3)
    ]
    
    for i in range(n_travel_days):
        s.add(Implies(travel[i], Or([And(city[i] == a, city[i+1] == b) for (a, b) in allowed_edges])))
        s.add(Implies(Not(travel[i]), city[i] == city[i+1]))
    
    s.add(Sum([If(travel[i], 1, 0) for i in range(n_travel_days)]) == 4)
    
    required_days = [6, 2, 7, 3, 5]
    for c_idx in range(5):
        total = 0
        for i in range(n_travel_days):
            total += If(travel[i], 
                        If(city[i] == c_idx, 1, 0) + If(city[i+1] == c_idx, 1, 0),
                        If(city[i] == c_idx, 1, 0))
        total += If(city[n_days-1] == c_idx, 1, 0)
        s.add(total == required_days[c_idx])
    
    s.add(city[6] == 2)
    s.add(Not(travel[6]))
    s.add(city[12] == 2)
    s.add(Not(travel[12]))
    
    wedding_constraints = []
    for j in range(6):
        cond = Or(city[j] == 0, 
                 And(travel[j], city[j+1] == 0))
        wedding_constraints.append(cond)
    s.add(Or(wedding_constraints))
    
    if s.check() == sat:
        m = s.model()
        schedule = []
        for i in range(n_days):
            if i < n_travel_days and is_true(m.eval(travel[i])):
                start_city = m.eval(city[i]).as_long()
                end_city = m.eval(city[i+1]).as_long()
                schedule.append(f"Day {i+1}: {cities[start_city]} and {cities[end_city]}")
            else:
                c_val = m.eval(city[i]).as_long()
                schedule.append(f"Day {i+1}: {cities[c_val]}")
        for day in schedule:
            print(day)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()