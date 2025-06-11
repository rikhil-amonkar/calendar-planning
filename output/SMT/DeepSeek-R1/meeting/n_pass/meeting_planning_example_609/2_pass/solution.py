from z3 import *

def main():
    # Define friends and their data
    n = 7
    names = ["David", "Kenneth", "John", "Charles", "Deborah", "Karen", "Carol"]
    min_duration = [45, 120, 15, 60, 90, 15, 30]
    available_start = [-60, 300, 480, 765, -120, 525, -45]
    available_end = [645, 645, 660, 825, 555, 735, 15]
    
    # Travel times from Chinatown to each friend's location
    start_travel = [18, 17, 10, 7, 23, 29, 19]
    
    # Travel times between friends' locations (7x7 matrix)
    between_travel = [
        [0, 11, 16, 15, 17, 24, 25],
        [10, 0, 10, 14, 9, 16, 18],
        [15, 10, 0, 12, 15, 21, 11],
        [14, 15, 15, 0, 22, 26, 24],
        [17, 10, 16, 22, 0, 10, 11],
        [24, 17, 21, 30, 11, 0, 16],
        [26, 18, 11, 22, 12, 15, 0]
    ]
    
    # Create Z3 variables
    meet = [Bool(f"meet_{i}") for i in range(n)]
    start = [Real(f"start_{i}") for i in range(n)]
    end = [Real(f"end_{i}") for i in range(n)]
    before = [[Bool(f"before_{i}_{j}") for j in range(n)] for i in range(n)]
    first = [Bool(f"first_{i}") for i in range(n)]
    
    opt = Optimize()
    
    # Meeting duration and availability constraints
    for i in range(n):
        opt.add(Implies(meet[i], end[i] == start[i] + min_duration[i]))
        opt.add(Implies(meet[i], start[i] >= available_start[i]))
        opt.add(Implies(meet[i], end[i] <= available_end[i]))
    
    # Explicitly fix Charles' meeting time to avoid any violation
    charles_index = names.index("Charles")
    opt.add(meet[charles_index])
    opt.add(start[charles_index] == 765)
    opt.add(end[charles_index] == 825)
    
    # Ordering constraints for pairs
    for i in range(n):
        for j in range(n):
            if i != j:
                opt.add(Implies(And(meet[i], meet[j]),
                              Or(And(before[i][j], Not(before[j][i])),
                                 And(Not(before[i][j]), before[j][i]))))
    
    # Transitivity constraints
    for i in range(n):
        for j in range(n):
            if i != j:
                for k in range(n):
                    if k != i and k != j:
                        opt.add(Implies(And(meet[i], meet[j], meet[k], before[i][j], before[j][k]),
                                              before[i][k]))
    
    # Define first meetings
    for i in range(n):
        opt.add(Implies(first[i], meet[i]))
        for j in range(n):
            if j != i:
                opt.add(Implies(first[i], Implies(meet[j], Not(before[j][i]))))
        expr = [meet[i]]
        for j in range(n):
            if j != i:
                expr.append(Implies(meet[j], Not(before[j][i])))
        opt.add(Implies(And(*expr), first[i]))
    
    # Travel constraints for first meetings
    for i in range(n):
        opt.add(Implies(And(meet[i], first[i]), start[i] >= start_travel[i]))
    
    # Travel constraints between consecutive meetings
    for i in range(n):
        for j in range(n):
            if i != j:
                opt.add(Implies(And(meet[i], meet[j], before[j][i]),
                                  start[i] >= end[j] + between_travel[j][i]))
    
    # Maximize the number of meetings
    num_meetings = Sum([If(meet[i], 1, 0) for i in range(n)])
    opt.maximize(num_meetings)
    
    # Check and print solution
    if opt.check() == sat:
        m = opt.model()
        schedule = []
        for i in range(n):
            if is_true(m.evaluate(meet[i])):
                start_val = m.evaluate(start[i])
                end_val = m.evaluate(end[i])
                schedule.append((names[i], start_val, end_val))
        schedule.sort(key=lambda x: float(str(x[1])))
        
        print("SOLUTION:")
        print("We can meet the following friends:")
        for name, start_time, end_time in schedule:
            start_min = float(str(start_time))
            end_min = float(str(end_time))
            # Convert minutes to time string for readability
            start_hour = 9 + (start_min // 60)
            start_minute = start_min % 60
            start_str = f"{int(start_hour)}:{int(start_minute):02d}"
            end_hour = 9 + (end_min // 60)
            end_minute = end_min % 60
            end_str = f"{int(end_hour)}:{int(end_minute):02d}"
            print(f"- {name}: Start at {start_str}, End at {end_str}")
        print(f"Total friends met: {len(schedule)}")
    else:
        print("SOLUTION:")
        print("No valid schedule found.")

if __name__ == "__main__":
    main()