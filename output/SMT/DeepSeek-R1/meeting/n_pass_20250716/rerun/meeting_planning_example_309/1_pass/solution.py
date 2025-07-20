from z3 import *

def main():
    # Decision variables for start times (in minutes after 7:00 AM)
    s0, s1, s2 = Ints('s0 s1 s2')  # s0: Nancy, s1: Mary, s2: Jessica
    meet0, meet1, meet2 = Bools('meet0 meet1 meet2')  # Whether we meet each friend
    
    # Constants (times in minutes from 7:00 AM)
    start_time = 120  # 9:00 AM is 120 minutes after 7:00 AM
    
    # Travel times from Financial District to each location
    travel_FD = [5, 17, 19]  # [Chinatown (Nancy), Alamo Square (Mary), Bayview (Jessica)]
    
    # Travel time matrix between locations (index: 0=Chinatown, 1=Alamo Square, 2=Bayview)
    travel = [
        [0, 17, 22],  # From Chinatown to [Chinatown, Alamo, Bayview]
        [16, 0, 16],  # From Alamo Square to [Chinatown, Alamo, Bayview]
        [18, 16, 0]   # From Bayview to [Chinatown, Alamo, Bayview]
    ]
    
    # Availability start and end times, and meeting durations
    avail_start = [150, 0, 255]    # [Nancy, Mary, Jessica]
    avail_end = [390, 840, 405]    # [Nancy, Mary, Jessica]
    durations = [90, 75, 45]       # [Nancy, Mary, Jessica]
    
    s = [s0, s1, s2]
    meet = [meet0, meet1, meet2]
    names = ["Nancy", "Mary", "Jessica"]
    locations = ["Chinatown", "Alamo Square", "Bayview"]
    
    # Initialize the optimizer
    opt = Optimize()
    
    # Constraints for each friend
    for i in range(3):
        # If meeting the friend, ensure start time is within availability and after travel from start
        opt.add(Implies(meet[i], 
                       And(s[i] >= max(avail_start[i], start_time + travel_FD[i]),
                       s[i] + durations[i] <= avail_end[i])))
    
    # Constraints for every pair of friends
    for i in range(3):
        for j in range(i+1, 3):
            both_met = And(meet[i], meet[j])
            # Option 1: i before j
            option1 = (s[j] >= s[i] + durations[i] + travel[i][j])
            # Option 2: j before i
            option2 = (s[i] >= s[j] + durations[j] + travel[j][i])
            opt.add(Implies(both_met, Or(option1, option2)))
    
    # Objective: maximize the number of meetings
    num_meetings = meet0 + meet1 + meet2
    opt.maximize(num_meetings)
    
    # Check for a solution
    if opt.check() == sat:
        m = opt.model()
        count = m.eval(num_meetings).as_long()
        result = []
        print("SOLUTION:")
        print(f"Total meetings: {count}")
        for i in range(3):
            if m.eval(meet[i]):
                start_val = m.eval(s[i]).as_long()
                hours = 7 + start_val // 60
                minutes = start_val % 60
                time_str = f"{hours}:{minutes:02d}"
                print(f"{names[i]} at {locations[i]}: met at {time_str}")
            else:
                print(f"{names[i]} at {locations[i]}: not met")
    else:
        print("SOLUTION:")
        print("No valid schedule found")

if __name__ == "__main__":
    main()