from z3 import *

def minutes_to_time(minutes):
    total_minutes = minutes
    hours = total_minutes // 60
    mins = total_minutes % 60
    total_hours = 9 + hours
    return f"{total_hours}:{mins:02d}"

def main():
    # Index: 0: Kevin (Alamo Square), 1: Kimberly (Russian Hill), 2: Joseph (Presidio), 3: Thomas (Financial District)
    friends = ['Kevin', 'Kimberly', 'Joseph', 'Thomas']
    
    # Travel time matrix between friends: [0,1,2,3] corresponding to the friends above.
    # Row i to column j: from friend i to friend j.
    T = [
        [0, 13, 18, 17],
        [15, 0, 14, 11],
        [18, 14, 0, 23],
        [17, 10, 22, 0]
    ]
    
    # Travel time from Sunset to each friend's location
    travel_from_sunset = [17, 24, 16, 30]
    
    # Durations for each friend (in minutes)
    durs = [75, 30, 45, 45]
    
    # Available time windows (start and end in minutes from 9:00 AM)
    # The effective start time is the maximum of travel time from Sunset and the friend's available start time.
    # Available start times: 
    #   Kevin: 8:15 AM -> -45 min from 9:00 AM -> but we use travel time (17) since we can't start before arriving.
    #   Kimberly: 8:45 AM -> -15 min -> use travel time (24)
    #   Joseph: 6:30 PM -> 570 min
    #   Thomas: 7:00 PM -> 600 min
    L_bound = [max(travel_from_sunset[i], [ -45, -15, 570, 600 ][i]) for i in range(4)]
    U_bound = [750, 210, 615, 765]  # End times: 9:30PM, 12:30PM, 7:15PM, 9:45PM in minutes
    
    # Create Z3 variables
    meet = [Bool(f'meet_{i}') for i in range(4)]
    s = [Int(f's_{i}') for i in range(4)]
    
    # Create solver with optimization
    opt = Optimize()
    
    # Constraints for each friend
    for i in range(4):
        # If we meet the friend, then the start time must be at least the effective start time
        opt.add(Implies(meet[i], s[i] >= L_bound[i]))
        # Meeting must end by the friend's available end time
        opt.add(Implies(meet[i], s[i] + durs[i] <= U_bound[i]))
    
    # Constraints for every pair of friends
    for i in range(4):
        for j in range(4):
            if i != j:
                # If both friends are met, then one must be scheduled after the other with travel time
                constraint = Or(
                    s[i] + durs[i] + T[i][j] <= s[j],
                    s[j] + durs[j] + T[j][i] <= s[i]
                )
                opt.add(Implies(And(meet[i], meet[j]), constraint))
    
    # Maximize the number of meetings
    num_meet = Sum([If(meet[i], 1, 0) for i in range(4)])
    opt.maximize(num_meet)
    
    # Solve
    if opt.check() == sat:
        m = opt.model()
        total_meet = m.evaluate(num_meet).as_long()
        print(f"Total friends met: {total_meet}")
        for i in range(4):
            if m.evaluate(meet[i]):
                start_val = m.evaluate(s[i]).as_long()
                end_val = start_val + durs[i]
                start_time = minutes_to_time(start_val)
                end_time = minutes_to_time(end_val)
                print(f"Meet {friends[i]} from {start_time} to {end_time}")
        # Print travel details from Sunset to the first meeting (not explicitly modeled but implied)
    else:
        print("No solution found")

if __name__ == '__main__':
    main()