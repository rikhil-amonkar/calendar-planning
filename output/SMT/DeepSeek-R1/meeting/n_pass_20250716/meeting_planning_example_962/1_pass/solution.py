from z3 import *

def main():
    # Travel matrix: 10x10, indices 0 to 9 correspond to:
    # 0: Castro, 1: Marina District, 2: Presidio, 3: North Beach, 4: Embarcadero, 
    # 5: Haight-Ashbury, 6: Golden Gate Park, 7: Alamo Square, 8: Financial District, 9: Sunset District
    travel_matrix = [
        [0, 21, 20, 20, 22, 6, 11, 8, 21, 17],
        [22, 0, 10, 11, 14, 16, 18, 15, 17, 19],
        [21, 11, 0, 18, 20, 15, 12, 19, 23, 15],
        [23, 9, 17, 0, 6, 18, 22, 16, 8, 27],
        [25, 12, 20, 5, 0, 21, 25, 19, 5, 30],
        [6, 17, 15, 19, 20, 0, 7, 5, 21, 15],
        [13, 16, 11, 23, 25, 7, 0, 9, 26, 10],
        [8, 15, 17, 15, 16, 5, 9, 0, 17, 16],
        [20, 15, 22, 7, 4, 19, 23, 17, 0, 30],
        [17, 21, 16, 28, 30, 15, 11, 17, 30, 0]
    ]
    
    # Friend data: indices 1 to 9
    available_start = [0] * 10
    available_end = [0] * 10
    min_duration = [0] * 10
    
    # Dummy meeting (index0) not used for friend data
    # Elizabeth (index1): Marina District
    available_start[1] = 600   # 7:00 PM (600 minutes from 9:00 AM)
    available_end[1] = 705     # 8:45 PM
    min_duration[1] = 105
    
    # Joshua (index2): Presidio
    available_start[2] = -30   # 8:30 AM
    available_end[2] = 255     # 1:15 PM
    min_duration[2] = 105
    
    # Timothy (index3): North Beach
    available_start[3] = 645   # 7:45 PM
    available_end[3] = 780     # 10:00 PM
    min_duration[3] = 90
    
    # David (index4): Embarcadero
    available_start[4] = 105   # 10:45 AM
    available_end[4] = 210     # 12:30 PM
    min_duration[4] = 30
    
    # Kimberly (index5): Haight-Ashbury
    available_start[5] = 465   # 4:45 PM
    available_end[5] = 750     # 9:30 PM
    min_duration[5] = 75
    
    # Lisa (index6): Golden Gate Park
    available_start[6] = 510   # 5:30 PM
    available_end[6] = 765     # 9:45 PM
    min_duration[6] = 45
    
    # Stephanie (index7): Alamo Square
    available_start[7] = 390   # 3:30 PM
    available_end[7] = 450     # 4:30 PM
    min_duration[7] = 30
    
    # Helen (index8): Financial District
    available_start[8] = 510   # 5:30 PM
    available_end[8] = 570     # 6:30 PM
    min_duration[8] = 45
    
    # Laura (index9): Sunset District
    available_start[9] = 525   # 5:45 PM
    available_end[9] = 735     # 9:15 PM
    min_duration[9] = 90
    
    # Friend names for output
    friend_names = {
        1: "Elizabeth at Marina District",
        2: "Joshua at Presidio",
        3: "Timothy at North Beach",
        4: "David at Embarcadero",
        5: "Kimberly at Haight-Ashbury",
        6: "Lisa at Golden Gate Park",
        7: "Stephanie at Alamo Square",
        8: "Helen at Financial District",
        9: "Laura at Sunset District"
    }
    
    s = Optimize()
    
    meet = [None] * 10
    start = [None] * 10
    end = [None] * 10
    
    # Dummy meeting (Castro at 9:00 AM)
    meet[0] = True
    start[0] = 0
    end[0] = 0
    
    for i in range(1, 10):
        meet[i] = Bool(f"meet_{i}")
        start[i] = Int(f"start_{i}")
        end[i] = start[i] + min_duration[i]
    
    # Time window constraints
    for i in range(1, 10):
        s.add(Implies(meet[i], start[i] >= available_start[i]))
        s.add(Implies(meet[i], end[i] <= available_end[i]))
    
    # Disjunctive constraints for all pairs (including dummy)
    for i in range(10):
        for j in range(10):
            if i == j:
                continue
            constraint = Or(
                end[i] + travel_matrix[i][j] <= start[j],
                end[j] + travel_matrix[j][i] <= start[i]
            )
            s.add(Implies(And(meet[i], meet[j]), constraint))
    
    objective = Sum([If(meet[i], 1, 0) for i in range(1, 10)])
    s.maximize(objective)
    
    if s.check() == sat:
        m = s.model()
        total_met = 0
        result_schedule = []
        for i in range(1, 10):
            if is_true(m.eval(meet[i])):
                total_met += 1
                start_min = m.eval(start[i]).as_long()
                hours = 9 + start_min // 60
                minutes = start_min % 60
                am_pm = "AM"
                if hours >= 12:
                    am_pm = "PM"
                    if hours > 12:
                        hours -= 12
                # Handle noon (12 PM) and midnight (not applicable here)
                if hours == 12:
                    am_pm = "PM"
                if hours == 0:
                    hours = 12
                    am_pm = "AM"
                end_min = start_min + min_duration[i]
                end_hours = 9 + end_min // 60
                end_minutes = end_min % 60
                end_am_pm = "AM"
                if end_hours >= 12:
                    end_am_pm = "PM"
                    if end_hours > 12:
                        end_hours -= 12
                if end_hours == 12:
                    end_am_pm = "PM"
                if end_hours == 0:
                    end_hours = 12
                    end_am_pm = "AM"
                result_schedule.append((
                    friend_names[i],
                    f"{hours}:{minutes:02d} {am_pm}",
                    f"{end_hours}:{end_minutes:02d} {end_am_pm}"
                ))
        
        print("SOLUTION:")
        print(f"Maximum number of friends met: {total_met}")
        for name, start_time, end_time in result_schedule:
            print(f"Meet {name} from {start_time} to {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()