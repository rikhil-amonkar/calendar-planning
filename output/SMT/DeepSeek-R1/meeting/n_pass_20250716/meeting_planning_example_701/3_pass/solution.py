from z3 import *

def main():
    locations = [
        "Mission District", 
        "The Castro", 
        "Nob Hill", 
        "Presidio", 
        "Marina District", 
        "Pacific Heights", 
        "Golden Gate Park", 
        "Chinatown", 
        "Richmond District"
    ]
    
    T = [
        [0, 7, 12, 25, 19, 16, 17, 16, 20],
        [7, 0, 16, 20, 21, 16, 11, 22, 16],
        [13, 17, 0, 17, 11, 8, 17, 6, 14],
        [26, 21, 18, 0, 11, 11, 12, 21, 7],
        [20, 22, 12, 10, 0, 7, 18, 15, 11],
        [15, 16, 8, 11, 6, 0, 15, 11, 12],
        [17, 13, 20, 11, 16, 16, 0, 23, 7],
        [17, 22, 9, 19, 12, 10, 23, 0, 20],
        [20, 16, 17, 7, 9, 10, 9, 20, 0]
    ]
    
    min_durations = [0, 120, 15, 45, 90, 90, 60, 30, 30]
    
    available_start = [0, 615, 0, 735, 450, 180, 705, 180, 255]
    available_end = [0, 735, 120, 795, 705, 540, 765, 600, 405]
    
    M = 1000
    
    s = Optimize()
    
    u = [Real(f'u_{i}') for i in range(9)]
    
    edges = []
    x_dict = {}
    for i in range(9):
        for j in range(1, 9):
            if i != j:
                edges.append((i, j))
                x_dict[(i, j)] = Bool(f'x_{i}_{j}')
    
    meet = [Bool(f'meet_{i}') for i in range(1, 9)]
    
    in_list = []
    for j in range(1, 9):
        total_in = 0
        for i in range(9):
            if i != j and (i, j) in x_dict:
                total_in += If(x_dict[(i, j)], 1, 0)
        in_list.append(total_in)
    
    out_0 = 0
    for j in range(1, 9):
        if (0, j) in x_dict:
            out_0 += If(x_dict[(0, j)], 1, 0)
    
    out_list = []
    for i in range(1, 9):
        total_out = 0
        for j in range(1, 9):
            if i != j and (i, j) in x_dict:
                total_out += If(x_dict[(i, j)], 1, 0)
        out_list.append(total_out)
    
    k = Sum([If(meet_i, 1, 0) for meet_i in meet])
    
    s.add(u[0] == 0)
    
    for idx in range(1, 9):
        s.add(meet[idx-1] == (in_list[idx-1] == 1))
    
    s.add(out_0 == If(k >= 1, 1, 0))
    s.add(Sum(in_list) == k)
    s.add(Sum(out_list) == k - out_0)
    
    for (i, j) in edges:
        if i == 0:
            s.add(u[j] >= T[i][j] - M * (1 - If(x_dict[(i, j)], 1, 0)))
        else:
            s.add(u[j] >= u[i] + min_durations[i] + T[i][j] - M * (1 - If(x_dict[(i, j)], 1, 0)))
    
    for j in range(1, 9):
        s.add(Implies(meet[j-1], And(u[j] >= available_start[j], u[j] + min_durations[j] <= available_end[j])))
    
    s.maximize(k)
    
    if s.check() == sat:
        m = s.model()
        num_met = m.evaluate(k).as_long()
        print(f"SOLUTION: We can meet {num_met} friends.")
        print("Schedule:")
        base_hour = 9
        for j in range(1, 9):
            if is_true(m.evaluate(meet[j-1])):
                start_val = m.evaluate(u[j])
                if isinstance(start_val, IntNumRef):
                    start_minutes = start_val.as_long()
                elif isinstance(start_val, RatNumRef):
                    start_minutes = float(start_val.numerator_as_long()) / float(start_val.denominator_as_long())
                else:
                    continue
                total_minutes = start_minutes
                hours = int(total_minutes // 60)
                minutes = int(total_minutes % 60)
                hour_of_day = base_hour + hours
                am_pm = "AM" if hour_of_day < 12 else "PM"
                if hour_of_day > 12:
                    hour_of_day -= 12
                elif hour_of_day == 0:
                    hour_of_day = 12
                print(f"  - {locations[j]}: starts at {hour_of_day}:{minutes:02d} {am_pm}, lasts {min_durations[j]} minutes")
    else:
        print("SOLUTION: No feasible schedule found.")

if __name__ == "__main__":
    main()