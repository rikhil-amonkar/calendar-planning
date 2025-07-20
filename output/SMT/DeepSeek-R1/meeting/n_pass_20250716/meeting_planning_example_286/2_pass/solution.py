from z3 import *

def main():
    # Initialize the solver
    opt = Optimize()
    
    # Start times in minutes from 9:00 AM
    s_c, s_r, s_k = Ints('s_c s_r s_k')
    # Booleans for whether we meet each friend
    meet_c, meet_r, meet_k = Bools('meet_c meet_r meet_k')
    # Position variables for the sequence of meetings
    p_c, p_r, p_k = Ints('p_c p_r p_k')
    
    # Travel times from Union Square to each district
    travel_US = {
        'c': 26,  # Union Square to Sunset District
        'r': 14,  # Union Square to Mission District
        'k': 15   # Union Square to Bayview
    }
    
    # Travel times between districts
    travel_between = {
        ('c', 'r'): 24,  # Sunset District to Mission District
        ('c', 'k'): 22,  # Sunset District to Bayview
        ('r', 'c'): 24,  # Mission District to Sunset District
        ('r', 'k'): 15,  # Mission District to Bayview
        ('k', 'c'): 23,  # Bayview to Sunset District
        ('k', 'r'): 13   # Bayview to Mission District
    }
    
    # Meeting durations in minutes
    dur_c = 30
    dur_r = 120
    dur_k = 120
    
    # Time window constraints (in minutes from 9:00 AM)
    # Carol: 10:15 AM (75) to 11:45 AM (165) -> meeting must end by 165, so start by 135 (165-30)
    opt.add(Implies(meet_c, And(s_c >= 75, s_c <= 135)))
    # Rebecca: 11:30 AM (150) to 8:15 PM (675) -> meeting must end by 675, so start by 555 (675-120)
    opt.add(Implies(meet_r, And(s_r >= 150, s_r <= 555)))
    # Karen: 12:45 PM (225) to 3:00 PM (360) -> meeting must end by 360, so start by 240 (360-120)
    opt.add(Implies(meet_k, And(s_k >= 225, s_k <= 240)))
    
    # Position constraints for meetings that occur
    friends = [
        ('c', meet_c, s_c, dur_c, p_c),
        ('r', meet_r, s_r, dur_r, p_r),
        ('k', meet_k, s_k, dur_k, p_k)
    ]
    
    # Each meeting that occurs has a position between 0 and 2
    for _, meet, _, _, p in friends:
        opt.add(Implies(meet, And(p >= 0, p <= 2)))
    
    # Distinct positions for meetings that occur
    for i in range(len(friends)):
        for j in range(i + 1, len(friends)):
            _, meet_i, _, _, p_i = friends[i]
            _, meet_j, _, _, p_j = friends[j]
            opt.add(Implies(And(meet_i, meet_j), p_i != p_j))
    
    # Travel constraints: from Union Square or from a previous meeting
    for i in range(len(friends)):
        key_i, meet_i, s_i, dur_i, p_i = friends[i]
        other_friends = [friends[j] for j in range(len(friends)) if j != i]
        # If meeting_i happens, it must either be first (position 0) or after another meeting
        or_terms = []
        # Option 1: first meeting, so travel from Union Square
        or_terms.append(And(p_i == 0, s_i >= travel_US[key_i]))
        # Option 2: after another meeting j
        for key_j, meet_j, s_j, dur_j, p_j in other_friends:
            travel_time = travel_between[(key_j, key_i)]
            term = And(meet_j, p_j == p_i - 1, s_i >= s_j + dur_j + travel_time)
            or_terms.append(term)
        opt.add(Implies(meet_i, Or(or_terms)))
    
    # Maximize the number of meetings
    num_meetings = If(meet_c, 1, 0) + If(meet_r, 1, 0) + If(meet_k, 1, 0)
    opt.maximize(num_meetings)
    
    # Solve the problem
    if opt.check() == sat:
        m = opt.model()
        print("SOLUTION:")
        # Convert minutes to time string
        def to_time(minutes):
            total_minutes = minutes
            hours = total_minutes // 60
            mins = total_minutes % 60
            am_pm = "AM" if hours < 12 else "PM"
            if hours > 12:
                hours -= 12
            return f"{int(hours)}:{int(mins):02d} {am_pm}"
        
        # Print meeting details
        if m.eval(meet_c):
            start_c = m.eval(s_c).as_long()
            end_c = start_c + dur_c
            print(f"Meet Carol at Sunset District from {to_time(start_c)} to {to_time(end_c)}")
        if m.eval(meet_r):
            start_r = m.eval(s_r).as_long()
            end_r = start_r + dur_r
            print(f"Meet Rebecca at Mission District from {to_time(start_r)} to {to_time(end_r)}")
        if m.eval(meet_k):
            start_k = m.eval(s_k).as_long()
            end_k = start_k + dur_k
            print(f"Meet Karen at Bayview from {to_time(start_k)} to {to_time(end_k)}")
        
        total_met = (1 if m.eval(meet_c) else 0) + (1 if m.eval(meet_r) else 0) + (1 if m.eval(meet_k) else 0)
        print(f"Total friends met: {total_met}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()