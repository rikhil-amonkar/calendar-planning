from z3 import *

def get_travel_time(c1, c2, travel_matrix):
    expr = None
    for i in range(6):
        for j in range(6):
            cond = And(c1 == i, c2 == j)
            val = travel_matrix[i][j]
            if expr is None:
                expr = If(cond, val, 0)
            else:
                expr = If(cond, val, expr)
    return expr

def main():
    city_vars = [Int(f"city_{i}") for i in range(6)]
    start_day = [Int(f"start_{i}") for i in range(6)]
    end_day = [Int(f"end_{i}") for i in range(6)]
    
    s = Solver()
    
    for i in range(6):
        s.add(city_vars[i] >= 0, city_vars[i] <= 5)
    s.add(Distinct(city_vars))
    
    days = [1, 3, 3, 2, 2, 2]
    d_arr = []
    for i in range(6):
        d_arr.append(If(city_vars[i] == 0, days[0],
                    If(city_vars[i] == 1, days[1],
                    If(city_vars[i] == 2, days[2],
                    If(city_vars[i] == 3, days[3],
                    If(city_vars[i] == 4, days[4], days[5]))))))
    
    s.add(start_day[0] == 1)
    for i in range(6):
        s.add(end_day[i] == start_day[i] + d_arr[i] - 1)
    
    travel_days = [
        [0, 1, 2, 2, 3, 2],
        [1, 0, 1, 2, 2, 3],
        [2, 1, 0, 1, 1, 2],
        [2, 2, 1, 0, 1, 1],
        [3, 2, 1, 1, 0, 2],
        [2, 3, 2, 1, 2, 0]
    ]
    
    for i in range(5):
        travel_time = get_travel_time(city_vars[i], city_vars[i+1], travel_days)
        # Include travel days in the stay period of departure city
        s.add(start_day[i+1] == end_day[i] + travel_time + 1)
    
    s.add(end_day[5] == 20)
    
    s.add(Or(*[city_vars[i] == 1 for i in range(6)]))
    s.add(Or(*[city_vars[i] == 2 for i in range(6)]))
    
    if s.check() == sat:
        m = s.model()
        city_map = {0: 'A', 1: 'B', 2: 'C', 3: 'D', 4: 'E', 5: 'F'}
        sequence = [city_map[m[city_vars[i]].as_long()] for i in range(6)]
        start_days = [m[start_day[i]].as_long() for i in range(6)]
        end_days = [m[end_day[i]].as_long() for i in range(6)]
        durations = [days[m[city_vars[i]].as_long()] for i in range(6)]
        
        print("Sequence of cities:", sequence)
        print("Start days:", start_days)
        print("End days:", end_days)
        print("Durations:", durations)
        print("Total days:", end_days[5])
    else:
        print("No solution found")

if __name__ == "__main__":
    main()