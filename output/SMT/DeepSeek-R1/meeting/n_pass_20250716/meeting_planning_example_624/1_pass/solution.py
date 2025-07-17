from z3 import *

def main():
    # Define the travel_time matrix for 7 locations (0: Golden Gate Park, 1: Fisherman's Wharf, etc.)
    travel_time = [
        [0, 24, 13, 23, 10, 24, 19],
        [25, 0, 26, 12, 20, 6, 7],
        [11, 24, 0, 20, 8, 20, 18],
        [23, 8, 22, 0, 17, 3, 7],
        [9, 19, 8, 16, 0, 15, 13],
        [22, 5, 22, 6, 16, 0, 4],
        [21, 7, 21, 9, 15, 5, 0]
    ]
    
    # Friend data: [name, location_index, available_start, available_end, min_duration]
    friends = [
        ("Laura", 1, 165, 750, 60),     # Fisherman's Wharf
        ("Karen", 2, 0, 300, 75),       # The Castro
        ("Elizabeth", 3, 195, 750, 75), # Chinatown
        ("Deborah", 4, 180, 360, 105),  # Alamo Square
        ("Jason", 5, 345, 600, 90),     # North Beach
        ("Steven", 6, 345, 570, 120)    # Russian Hill
    ]
    
    n = len(friends)
    meet = [Bool(f'meet_{i}') for i in range(n)]
    start = [Int(f'start_{i}') for i in range(n)]
    
    s = Optimize()
    
    # Add constraints for each friend
    for i, (name, loc_idx, av_start, av_end, dur) in enumerate(friends):
        s.add(Implies(meet[i], start[i] >= av_start))
        s.add(Implies(meet[i], start[i] + dur <= av_end))
        s.add(Implies(meet[i], start[i] >= travel_time[0][loc_idx]))
    
    # Add disjunctive constraints for every pair of friends
    for i in range(n):
        for j in range(i + 1, n):
            _, loc_i, _, _, dur_i = friends[i]
            _, loc_j, _, _, dur_j = friends[j]
            constraint1 = start[i] + dur_i + travel_time[loc_i][loc_j] <= start[j]
            constraint2 = start[j] + dur_j + travel_time[loc_j][loc_i] <= start[i]
            s.add(Or(Not(meet[i]), Not(meet[j]), constraint1, constraint2))
    
    # Objective: maximize the number of friends met
    objective = Sum([If(meet[i], 1, 0) for i in range(n)])
    s.maximize(objective)
    
    # Check and print the solution
    if s.check() == sat:
        m = s.model()
        total_met = 0
        schedule = []
        for i, (name, _, _, _, dur) in enumerate(friends):
            if m.evaluate(meet[i]):
                total_met += 1
                s_val = m.evaluate(start[i])
                if isinstance(s_val, IntNumRef):
                    start_min = s_val.as_long()
                else:
                    start_min = s_val
                end_min = start_min + dur
                # Convert minutes to time string
                start_hour = 9 + start_min // 60
                start_minute = start_min % 60
                end_hour = 9 + end_min // 60
                end_minute = end_min % 60
                start_str = f"{start_hour}:{start_minute:02d}"
                end_str = f"{end_hour}:{end_minute:02d}"
                schedule.append(f"Meet {name} from {start_str} to {end_str}")
        print(f"SOLUTION: Met {total_met} friends.")
        for event in schedule:
            print(event)
    else:
        print("SOLUTION: No valid schedule found.")

if __name__ == "__main__":
    main()