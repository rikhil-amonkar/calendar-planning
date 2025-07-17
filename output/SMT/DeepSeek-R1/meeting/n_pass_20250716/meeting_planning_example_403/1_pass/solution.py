from z3 import *

def main():
    opt = Optimize()
    
    meet = [True]  # meet[0] is the virtual meeting at Union Square, always True
    start = [0]    # start[0] = 0 (9:00 AM in minutes)
    min_dur = [0, 75, 15, 60, 90, 30]  # minimum durations: [virtual, Andrew, Sarah, Nancy, Rebecca, Robert]
    win_start = [0, 165, 435, 510, 45, -30]  # window start times in minutes from 9:00 AM
    win_end = [0, 330, 585, 615, 750, 315]   # window end times in minutes from 9:00 AM

    # Initialize variables for meetings 1 to 5
    meet_vars = []
    start_vars = []
    for i in range(1, 6):
        meet_vars.append(Bool(f"meet_{i}"))
        start_vars.append(Int(f"start_{i}"))
    meet.extend(meet_vars)
    start.extend(start_vars)
    
    # Travel time matrix (6x6): [from_location][to_location]
    travel_time = [
        [0, 22, 15, 24, 7, 19],
        [22, 0, 16, 11, 23, 13],
        [12, 15, 0, 11, 11, 16],
        [22, 12, 11, 0, 21, 21],
        [7, 23, 10, 19, 0, 22],
        [19, 11, 16, 20, 20, 0]
    ]
    
    # Constraints for each meeting (1 to 5)
    for i in range(1, 6):
        # Meeting must be within time window
        opt.add(Implies(meet[i], start[i] >= win_start[i]))
        opt.add(Implies(meet[i], start[i] + min_dur[i] <= win_end[i]))
        # Travel time from Union Square (virtual meeting) to meeting i
        opt.add(Implies(meet[i], start[i] >= travel_time[0][i]))
    
    # Pairwise constraints for meetings 1 to 5
    before_vars = {}
    for i in range(1, 6):
        for j in range(i + 1, 6):
            before_ij = Bool(f"before_{i}_{j}")
            before_vars[(i, j)] = before_ij
            # If both meetings are chosen, enforce travel time based on order
            opt.add(Implies(And(meet[i], meet[j]),
                            If(before_ij,
                               start[i] + min_dur[i] + travel_time[i][j] <= start[j],
                               start[j] + min_dur[j] + travel_time[j][i] <= start[i])))
    
    # Maximize the number of meetings
    num_meet = Sum([If(meet[i], 1, 0) for i in range(1, 6)])
    opt.maximize(num_meet)
    
    if opt.check() == sat:
        m = opt.model()
        total_meet = m.evaluate(num_meet)
        print(f"Total meetings: {total_meet}")
        for i in range(1, 6):
            if m.evaluate(meet[i]):
                start_val = m.evaluate(start[i])
                hours = start_val // 60
                minutes = start_val % 60
                start_time = f"{9 + hours}:{minutes:02d}AM" if hours < 3 else f"{9 + hours - 12}:{minutes:02d}PM"
                end_val = start_val + min_dur[i]
                hours_end = end_val // 60
                minutes_end = end_val % 60
                end_time = f"{9 + hours_end}:{minutes_end:02d}AM" if hours_end < 3 else f"{9 + hours_end - 12}:{minutes_end:02d}PM"
                names = ["Andrew (Golden Gate Park)", "Sarah (Pacific Heights)", "Nancy (Presidio)", "Rebecca (Chinatown)", "Robert (The Castro)"]
                print(f"Meet {names[i-1]} from {start_time} to {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()