from z3 import *
from itertools import permutations, combinations

class Friend:
    def __init__(self, name, location, avail_start, avail_end, min_time):
        self.name = name
        self.location = location
        self.avail_start = avail_start
        self.avail_end = avail_end
        self.min_time = min_time

def main():
    travel_time_dict = {
        "FW": {"GGP": 25, "P": 17, "RD": 18},
        "GGP": {"FW": 24, "P": 11, "RD": 7},
        "P": {"FW": 19, "GGP": 12, "RD": 7},
        "RD": {"FW": 18, "GGP": 9, "P": 7}
    }
    
    M = Friend("Melissa", "GGP", -30, 660, 15)
    E = Friend("Emily", "RD", 465, 780, 120)
    N = Friend("Nancy", "P", 645, 780, 105)
    all_friends = [M, E, N]
    
    best_count = 0
    best_schedule = None
    best_order = None
    
    # Try meeting all three friends
    found_three = False
    for perm in permutations(all_friends):
        s = Solver()
        T0, T1, T2 = Reals('T0 T1 T2')
        loc0 = perm[0].location
        travel0 = travel_time_dict["FW"][loc0]
        s.add(T0 >= travel0, T0 >= perm[0].avail_start, T0 + perm[0].min_time <= perm[0].avail_end)
        
        loc1 = perm[1].location
        travel1 = travel_time_dict[loc0][loc1]
        s.add(T1 >= T0 + perm[0].min_time + travel1, T1 >= perm[1].avail_start, T1 + perm[1].min_time <= perm[1].avail_end)
        
        loc2 = perm[2].location
        travel2 = travel_time_dict[loc1][loc2]
        s.add(T2 >= T1 + perm[1].min_time + travel2, T2 >= perm[2].avail_start, T2 + perm[2].min_time <= perm[2].avail_end)
        
        if s.check() == sat:
            m = s.model()
            times = [m[T0].as_fraction(), m[T1].as_fraction(), m[T2].as_fraction()]
            best_count = 3
            best_schedule = times
            best_order = perm
            found_three = True
            break
    
    if not found_three:
        found_two = False
        for combo in combinations(all_friends, 2):
            for perm in permutations(combo):
                s = Solver()
                T0, T1 = Reals('T0 T1')
                loc0 = perm[0].location
                travel0 = travel_time_dict["FW"][loc0]
                s.add(T0 >= travel0, T0 >= perm[0].avail_start, T0 + perm[0].min_time <= perm[0].avail_end)
                
                loc1 = perm[1].location
                travel1 = travel_time_dict[loc0][loc1]
                s.add(T1 >= T0 + perm[0].min_time + travel1, T1 >= perm[1].avail_start, T1 + perm[1].min_time <= perm[1].avail_end)
                
                if s.check() == sat:
                    m = s.model()
                    times = [m[T0].as_fraction(), m[T1].as_fraction()]
                    best_count = 2
                    best_schedule = times
                    best_order = perm
                    found_two = True
                    break
            if found_two:
                break
        
        if not found_two:
            for friend in all_friends:
                s = Solver()
                T0 = Real('T0')
                loc0 = friend.location
                travel0 = travel_time_dict["FW"][loc0]
                s.add(T0 >= travel0, T0 >= friend.avail_start, T0 + friend.min_time <= friend.avail_end)
                if s.check() == sat:
                    m = s.model()
                    time0 = m[T0].as_fraction()
                    best_count = 1
                    best_schedule = [time0]
                    best_order = [friend]
                    break
    
    print("SOLUTION:")
    if best_count == 3:
        print(f"Start at Fisherman's Wharf at 9:00 AM.")
        for i in range(3):
            friend = best_order[i]
            start_time = float(best_schedule[i])
            total_minutes = start_time
            abs_hour = 9 + int(total_minutes) // 60
            abs_minute = int(total_minutes) % 60
            if abs_hour >= 13:
                hour_str = str(abs_hour - 12)
                am_pm = "PM"
            elif abs_hour == 12:
                hour_str = "12"
                am_pm = "PM"
            else:
                hour_str = str(abs_hour)
                am_pm = "AM"
            print(f"Travel to {friend.location} to meet {friend.name} at {hour_str}:{abs_minute:02d} {am_pm} for at least {friend.min_time} minutes.")
    elif best_count == 2:
        print(f"Start at Fisherman's Wharf at 9:00 AM.")
        for i in range(2):
            friend = best_order[i]
            start_time = float(best_schedule[i])
            total_minutes = start_time
            abs_hour = 9 + int(total_minutes) // 60
            abs_minute = int(total_minutes) % 60
            if abs_hour >= 13:
                hour_str = str(abs_hour - 12)
                am_pm = "PM"
            elif abs_hour == 12:
                hour_str = "12"
                am_pm = "PM"
            else:
                hour_str = str(abs_hour)
                am_pm = "AM"
            print(f"Travel to {friend.location} to meet {friend.name} at {hour_str}:{abs_minute:02d} {am_pm} for at least {friend.min_time} minutes.")
    elif best_count == 1:
        friend = best_order[0]
        start_time = float(best_schedule[0])
        total_minutes = start_time
        abs_hour = 9 + int(total_minutes) // 60
        abs_minute = int(total_minutes) % 60
        if abs_hour >= 13:
            hour_str = str(abs_hour - 12)
            am_pm = "PM"
        elif abs_hour == 12:
            hour_str = "12"
            am_pm = "PM"
        else:
            hour_str = str(abs_hour)
            am_pm = "AM"
        print(f"Start at Fisherman's Wharf at 9:00 AM.")
        print(f"Travel to {friend.location} to meet {friend.name} at {hour_str}:{abs_minute:02d} {am_pm} for at least {friend.min_time} minutes.")
    else:
        print("Unable to meet any friends.")

if __name__ == '__main__':
    main()