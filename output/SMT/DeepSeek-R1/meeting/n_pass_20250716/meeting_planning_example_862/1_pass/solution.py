from z3 import *

def main():
    # Travel time matrix: 10x10, indices: 
    # 0: Mission District, 1: Alamo Square, 2: Presidio, 3: Russian Hill, 4: North Beach,
    # 5: Golden Gate Park, 6: Richmond District, 7: Embarcadero, 8: Financial District, 9: Marina District
    T = [
        [0, 11, 25, 15, 17, 17, 20, 19, 15, 19],
        [10, 0, 17, 13, 15, 9, 11, 16, 17, 15],
        [26, 19, 0, 14, 18, 12, 7, 20, 23, 11],
        [16, 15, 14, 0, 5, 21, 14, 8, 11, 7],
        [18, 16, 17, 4, 0, 22, 18, 6, 8, 9],
        [17, 9, 11, 19, 23, 0, 7, 25, 26, 16],
        [20, 13, 7, 13, 17, 9, 0, 19, 22, 9],
        [20, 19, 20, 8, 5, 25, 21, 0, 5, 12],
        [17, 17, 22, 11, 7, 23, 21, 4, 0, 15],
        [20, 15, 10, 8, 11, 18, 11, 14, 17, 0]
    ]
    
    friends = [
        ("Laura", "Alamo Square", 330, 435, 75),        # 0: 2:30PM to 4:15PM
        ("Brian", "Presidio", 75, 480, 30),             # 1: 10:15AM to 5:00PM
        ("Karen", "Russian Hill", 540, 675, 90),         # 2: 6:00PM to 8:15PM
        ("Stephanie", "North Beach", 75, 420, 75),       # 3: 10:15AM to 4:00PM
        ("Helen", "Golden Gate Park", 150, 765, 120),    # 4: 11:30AM to 9:45PM
        ("Sandra", "Richmond District", 0, 375, 30),     # 5: 8:00AM to 3:15PM (available from 9:00AM)
        ("Mary", "Embarcadero", 465, 585, 120),          # 6: 4:45PM to 6:45PM
        ("Deborah", "Financial District", 600, 705, 105),# 7: 7:00PM to 8:45PM
        ("Elizabeth", "Marina District", 0, 255, 105)    # 8: 8:30AM to 1:15PM (available from 9:00AM)
    ]
    
    n = len(friends)
    met = [Bool(f'met_{i}') for i in range(n)]
    start = [Int(f'start_{i}') for i in range(n)]
    
    s = Optimize()
    
    # Constraints for each friend
    for i in range(n):
        # Location index for friend i: i+1 (since Mission is 0)
        loc_index = i+1
        travel_from_mission = T[0][loc_index]
        available_start = friends[i][2]
        available_end = friends[i][3]
        min_dur = friends[i][4]
        
        # If met, then constraints
        s.add(Implies(met[i], start[i] >= travel_from_mission))
        s.add(Implies(met[i], start[i] >= available_start))
        end_i = start[i] + min_dur
        s.add(Implies(met[i], end_i <= available_end))
        s.add(Implies(met[i], start[i] >= 0))
    
    # Pairwise constraints for friends that are both met
    for i in range(n):
        for j in range(i+1, n):
            loc_i = i+1
            loc_j = j+1
            min_dur_i = friends[i][4]
            min_dur_j = friends[j][4]
            end_i = start[i] + min_dur_i
            end_j = start[j] + min_dur_j
            # Option 1: i before j: start_j >= end_i + travel from i to j
            opt1 = start[j] >= end_i + T[loc_i][loc_j]
            # Option 2: j before i: start_i >= end_j + travel from j to i
            opt2 = start[i] >= end_j + T[loc_j][loc_i]
            s.add(Implies(And(met[i], met[j]), Or(opt1, opt2)))
    
    # Maximize the number of friends met
    total_met = Sum([If(met[i], 1, 0) for i in range(n)])
    s.maximize(total_met)
    
    if s.check() == sat:
        m = s.model()
        num_met = m.evaluate(total_met)
        print(f"Maximum friends met: {num_met}")
        
        # Print schedule in chronological order
        schedule = []
        for i in range(n):
            if is_true(m.evaluate(met[i])):
                start_val = m.evaluate(start[i])
                if isinstance(start_val, IntNumRef):
                    start_min = start_val.as_long()
                else:
                    start_min = start_val
                end_min = start_min + friends[i][4]
                schedule.append((friends[i][0], start_min, end_min))
        
        # Sort by start time
        schedule.sort(key=lambda x: x[1])
        
        def minutes_to_time(mins):
            total_mins = mins
            hours = 9 + total_mins // 60
            mins_part = total_mins % 60
            return f"{hours}:{mins_part:02d}"
        
        for friend, start_min, end_min in schedule:
            start_str = minutes_to_time(start_min)
            end_str = minutes_to_time(end_min)
            print(f"Meet {friend} from {start_str} to {end_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()