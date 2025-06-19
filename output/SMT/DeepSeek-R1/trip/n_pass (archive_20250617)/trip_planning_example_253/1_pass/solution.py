from z3 import *

def main():
    # Define the 15 variables: x0 to x14 (for x1 to x15)
    x = [Int('x%d' % i) for i in range(15)]
    
    s = Solver()
    
    # Each x_i must be in [0,3]
    for i in range(15):
        s.add(x[i] >= 0)
        s.add(x[i] <= 3)
    
    # Direct flights: set of allowed pairs (a,b) for a direct flight (if a != b)
    edges = [(0,1), (1,0), (0,2), (2,0), (0,3), (3,0), (1,2), (2,1), (1,3), (3,1)]
    # For each consecutive pair (x_i, x_{i+1]) for i in 0 to 13
    for i in range(14):
        # If x[i] != x[i+1], then (x[i], x[i+1]) must be in edges
        s.add(If(x[i] != x[i+1],
                 Or([And(x[i] == a, x[i+1] == b) for (a, b) in edges]),
                 True))
    
    # Total days per city:
    # Amsterdam (0)
    starts0 = Sum([If(x[i] == 0, 1, 0) for i in range(14)])   # x0 to x13 (start of day1 to start of day14)
    ends0   = Sum([If(x[i] == 0, 1, 0) for i in range(1, 15)]) # x1 to x14 (end of day1 to end of day14)
    non_travel0 = Sum([If(And(x[i] == 0, x[i+1] == 0), 1, 0) for i in range(14)]) # non-travel days in Amsterdam
    total0 = starts0 + ends0 - non_travel0
    s.add(total0 == 3)
    
    # Vienna (1)
    starts1 = Sum([If(x[i] == 1, 1, 0) for i in range(14)])
    ends1   = Sum([If(x[i] == 1, 1, 0) for i in range(1, 15)])
    non_travel1 = Sum([If(And(x[i] == 1, x[i+1] == 1), 1, 0) for i in range(14)])
    total1 = starts1 + ends1 - non_travel1
    s.add(total1 == 7)
    
    # Santorini (2)
    starts2 = Sum([If(x[i] == 2, 1, 0) for i in range(14)])
    ends2   = Sum([If(x[i] == 2, 1, 0) for i in range(1, 15)])
    non_travel2 = Sum([If(And(x[i] == 2, x[i+1] == 2), 1, 0) for i in range(14)])
    total2 = starts2 + ends2 - non_travel2
    s.add(total2 == 4)
    
    # Lyon (3)
    starts3 = Sum([If(x[i] == 3, 1, 0) for i in range(14)])
    ends3   = Sum([If(x[i] == 3, 1, 0) for i in range(1, 15)])
    non_travel3 = Sum([If(And(x[i] == 3, x[i+1] == 3), 1, 0) for i in range(14)])
    total3 = starts3 + ends3 - non_travel3
    s.add(total3 == 3)
    
    # Workshop in Amsterdam: between day9 and day11 (days 9,10,11) -> we require at least one of the days has Amsterdam.
    # Day9: start x8, end x9 -> Amsterdam if x8==0 or x9==0.
    # Day10: x9==0 or x10==0
    # Day11: x10==0 or x11==0
    s.add(Or(Or(x[8] == 0, x[9] == 0), Or(x[9] == 0, x[10] == 0), Or(x[10] == 0, x[11] == 0)))
    
    # Wedding in Lyon: between day7 and day9 (days 7,8,9)
    # Day7: x6 or x7
    # Day8: x7 or x8
    # Day9: x8 or x9
    s.add(Or(Or(x[6] == 3, x[7] == 3), Or(x[7] == 3, x[8] == 3), Or(x[8] == 3, x[9] == 3)))
    
    if s.check() == sat:
        m = s.model()
        sol = [m.evaluate(x[i]).as_long() for i in range(15)]
        city_names = ['Amsterdam', 'Vienna', 'Santorini', 'Lyon']
        print("Day-by-day itinerary:")
        for day in range(1, 15):
            start_city = sol[day-1]
            end_city = sol[day]
            if start_city == end_city:
                print(f"Day {day}: Stay in {city_names[start_city]}")
            else:
                print(f"Day {day}: Travel from {city_names[start_city]} to {city_names[end_city]} (thus in both cities on day {day})")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()