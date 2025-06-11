from z3 import *
import itertools

# Travel matrix: 9x9. Locations: 
# 0: Marina District, 1: The Castro, 2: Fisherman's Wharf, 3: Bayview, 
# 4: Pacific Heights, 5: Mission District, 6: Alamo Square, 7: Golden Gate Park, 8: Presidio
travel_matrix = [
    [0, 22, 10, 27, 7, 20, 15, 18, 10],
    [21, 0, 24, 19, 16, 7, 8, 11, 20],
    [9, 27, 0, 26, 12, 22, 21, 25, 17],
    [27, 19, 25, 0, 23, 13, 16, 22, 32],
    [6, 16, 13, 22, 0, 15, 10, 15, 11],
    [19, 7, 22, 14, 16, 0, 11, 17, 25],
    [15, 8, 19, 16, 10, 10, 0, 9, 17],
    [16, 13, 24, 23, 16, 17, 9, 0, 11],
    [11, 21, 19, 31, 11, 26, 19, 12, 0]
]

# Friend data: index, name, min_duration (minutes), window_start (minutes from 9:00), window_end (minutes from 9:00)
friends = [
    (0, "Amanda", 105, 345, 630),    # Marina District: 2:45PM-7:30PM -> 345 to 630 minutes
    (1, "Melissa", 30, 30, 480),      # The Castro: 9:30AM-5:00PM -> 30 to 480 minutes
    (2, "Jeffrey", 120, 225, 585),    # Fisherman's Wharf: 12:45PM-6:45PM -> 225 to 585 minutes
    (3, "Matthew", 30, 75, 255),      # Bayview: 10:15AM-1:15PM -> 75 to 255 minutes
    (4, "Nancy", 105, 480, 750),     # Pacific Heights: 5:00PM-9:30PM -> 480 to 750 minutes
    (5, "Karen", 105, 510, 690),     # Mission District: 5:30PM-8:30PM -> 510 to 690 minutes
    (6, "Robert", 120, 135, 510),    # Alamo Square: 11:15AM-5:30PM -> 135 to 510 minutes
    (7, "Joseph", 105, -30, 735)     # Golden Gate Park: 8:30AM-9:15PM -> -30 to 735 minutes (earliest start is 12 minutes after 9:00)
]

min_duration_list = [105, 30, 120, 30, 105, 105, 120, 105]
window_start_list = [345, 30, 225, 75, 480, 510, 135, -30]
window_end_list = [630, 480, 585, 255, 750, 690, 510, 735]

def get_min_duration(j):
    return If(j == 0, min_duration_list[0],
           If(j == 1, min_duration_list[1],
           If(j == 2, min_duration_list[2],
           If(j == 3, min_duration_list[3],
           If(j == 4, min_duration_list[4],
           If(j == 5, min_duration_list[5],
           If(j == 6, min_duration_list[6],
           If(j == 7, min_duration_list[7], 0)))))))

def get_window_start(j):
    return If(j == 0, window_start_list[0],
           If(j == 1, window_start_list[1],
           If(j == 2, window_start_list[2],
           If(j == 3, window_start_list[3],
           If(j == 4, window_start_list[4],
           If(j == 5, window_start_list[5],
           If(j == 6, window_start_list[6],
           If(j == 7, window_start_list[7], 0)))))))

def get_window_end(j):
    return If(j == 0, window_end_list[0],
           If(j == 1, window_end_list[1],
           If(j == 2, window_end_list[2],
           If(j == 3, window_end_list[3],
           If(j == 4, window_end_list[4],
           If(j == 5, window_end_list[5],
           If(j == 6, window_end_list[6],
           If(j == 7, window_end_list[7], 0)))))))

def travel_time_z3(i, j):
    expr = IntVal(0)
    for src in range(8, -1, -1):
        for dst in range(8, -1, -1):
            expr = If(And(i == src, j == dst), travel_matrix[src][dst], expr)
    return expr

def minutes_to_time(minutes):
    total_minutes = minutes
    hours = total_minutes // 60
    minutes_remaining = total_minutes % 60
    hour_clock = 9 + hours
    if hour_clock >= 12:
        period = "PM"
        if hour_clock > 12:
            hour_clock -= 12
    else:
        period = "AM"
    return f"{hour_clock}:{minutes_remaining:02d}{period}"

def schedule_subset(subset):
    k = len(subset)
    s = Solver()
    order = [Int(f'order_{i}') for i in range(k)]
    start_order = [Int(f'start_{i}') for i in range(k)]
    
    for i in range(k):
        s.add(Or([order[i] == j for j in subset]))
    s.add(Distinct(order))
    
    for i in range(k):
        s.add(start_order[i] >= 0)
    
    j0 = order[0]
    travel_time0 = travel_time_z3(8, j0)
    min_dur0 = get_min_duration(j0)
    w_start0 = get_window_start(j0)
    w_end0 = get_window_end(j0)
    s.add(start_order[0] >= travel_time0)
    s.add(start_order[0] >= w_start0)
    s.add(start_order[0] + min_dur0 <= w_end0)
    
    for i in range(1, k):
        j_prev = order[i-1]
        j_curr = order[i]
        travel_time_ij = travel_time_z3(j_prev, j_curr)
        min_dur_prev = get_min_duration(j_prev)
        min_dur_curr = get_min_duration(j_curr)
        w_start_curr = get_window_start(j_curr)
        w_end_curr = get_window_end(j_curr)
        arrival_time = start_order[i-1] + min_dur_prev + travel_time_ij
        s.add(start_order[i] >= arrival_time)
        s.add(start_order[i] >= w_start_curr)
        s.add(start_order[i] + min_dur_curr <= w_end_curr)
    
    if s.check() == sat:
        model = s.model()
        order_eval = [model.evaluate(order[i]).as_long() for i in range(k)]
        start_order_eval = [model.evaluate(start_order[i]).as_long() for i in range(k)]
        schedule = []
        for i in range(k):
            friend_idx = order_eval[i]
            start_time_minutes = start_order_eval[i]
            end_time_minutes = start_time_minutes + min_duration_list[friend_idx]
            schedule.append((friends[friend_idx][1], start_time_minutes, end_time_minutes))
        return schedule, order_eval
    return None, None

def main():
    all_friends = [0,1,2,3,4,5,6,7]
    for k in range(8, 0, -1):
        for subset in itertools.combinations(all_friends, k):
            schedule, order = schedule_subset(subset)
            if schedule is not None:
                print("SOLUTION:")
                print(f"Met {k} friends in the following order: {[friends[idx][1] for idx in order]}")
                for name, start, end in schedule:
                    start_time = minutes_to_time(start)
                    end_time = minutes_to_time(end)
                    print(f"Meet {name} from {start_time} to {end_time}")
                return
    print("SOLUTION: No feasible schedule found to meet any friends.")

if __name__ == "__main__":
    main()