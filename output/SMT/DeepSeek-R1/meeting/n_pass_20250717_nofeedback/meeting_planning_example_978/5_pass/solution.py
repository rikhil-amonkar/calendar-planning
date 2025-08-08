from z3 import *
import json

def main():
    # Friend data: [name, location, start_minutes, end_minutes, duration_minutes, travel0]
    friends_data = [
        ("Stephanie", "Fisherman's Wharf", 15*60+30, 22*60, 30, 6),
        ("Lisa", "Financial District", 10*60+45, 17*60+15, 15, 5),
        ("Melissa", "Russian Hill", 17*60, 21*60+45, 120, 8),
        ("Betty", "Marina District", 10*60+45, 14*60+15, 60, 12),
        ("Sarah", "Richmond District", 16*60+15, 19*60+30, 105, 21),
        ("Daniel", "Pacific Heights", 18*60+30, 21*60+45, 60, 11),
        ("Joshua", "Haight-Ashbury", 9*60, 15*60+30, 15, 21),
        ("Joseph", "Presidio", 7*60, 13*60, 45, 20),
        ("Andrew", "Nob Hill", 19*60+45, 22*60, 105, 10),
        ("John", "The Castro", 13*60+15, 19*60+45, 45, 25)
    ]
    
    names = [fd[0] for fd in friends_data]
    start_minutes = [fd[2] for fd in friends_data]
    end_minutes = [fd[3] for fd in friends_data]
    duration_minutes = [fd[4] for fd in friends_data]
    travel0 = [fd[5] for fd in friends_data]
    
    # Travel matrix between friends (10x10) - use as provided (asymmetric)
    travel_matrix = [
        [0, 11, 7, 9, 18, 12, 22, 17, 11, 27],   # Fisherman's Wharf (0)
        [10, 0, 11, 15, 21, 13, 19, 22, 8, 20],   # Financial District (1)
        [7, 11, 0, 7, 14, 7, 17, 14, 5, 21],      # Russian Hill (2)
        [10, 17, 8, 0, 11, 7, 16, 10, 12, 22],    # Marina District (3)
        [18, 22, 13, 9, 0, 10, 10, 7, 17, 16],    # Richmond District (4)
        [13, 13, 7, 6, 12, 0, 11, 11, 8, 16],     # Pacific Heights (5)
        [23, 21, 17, 17, 10, 12, 0, 15, 15, 6],   # Haight-Ashbury (6)
        [19, 23, 14, 11, 7, 11, 15, 0, 18, 21],   # Presidio (7)
        [10, 9, 5, 11, 14, 8, 13, 17, 0, 17],     # Nob Hill (8)
        [24, 21, 18, 21, 16, 16, 6, 20, 16, 0]    # The Castro (9)
    ]
    
    s = Optimize()
    s.set("timeout", 300000)  # 5 minutes timeout

    n = len(names)
    do_meet = [Bool(f"do_meet_{i}") for i in range(n)]
    s_time = [Int(f"s_time_{i}") for i in range(n)]  # start time in minutes
    e_time = [s_time[i] + duration_minutes[i] for i in range(n)]  # end time in minutes
    
    # Time window constraints
    for i in range(n):
        s.add(Implies(do_meet[i], 
                     And(s_time[i] >= start_minutes[i],
                         e_time[i] <= end_minutes[i])))
    
    # Joseph must start at or after 9:20 AM (560 minutes)
    s.add(Implies(do_meet[7], s_time[7] >= 9*60+20))
    
    # First meeting constraint
    for i in range(n):
        s.add(Implies(do_meet[i], s_time[i] >= 9*60 + travel0[i]))
    
    # Travel time constraints between all pairs of meetings
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            # Either i is before j, or j is before i, or they don't overlap
            before = And(do_meet[i], do_meet[j], e_time[i] + travel_matrix[i][j] <= s_time[j])
            after = And(do_meet[i], do_meet[j], e_time[j] + travel_matrix[j][i] <= s_time[i])
            s.add(Or(Not(do_meet[i]), Not(do_meet[j]), before, after))
    
    # Objective: maximize the number of meetings
    num_meetings = Sum([If(do_meet[i], 1, 0) for i in range(n)])
    s.maximize(num_meetings)
    
    if s.check() == sat:
        m = s.model()
        meeting_list = []
        for i in range(n):
            if is_true(m.eval(do_meet[i])):
                start_val = m.eval(s_time[i]).as_long()
                end_val = start_val + duration_minutes[i]
                start_str = f"{start_val//60:02d}:{start_val%60:02d}"
                end_str = f"{end_val//60:02d}:{end_val%60:02d}"
                meeting_list.append({
                    "action": "meet",
                    "person": names[i],
                    "start_time": start_str,
                    "end_time": end_str
                })
        # Sort meetings by start time
        meeting_list.sort(key=lambda x: x["start_time"])
        result = {"itinerary": meeting_list}
        print("SOLUTION:")
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()