from z3 import *

def main():
    # Travel time matrix: 4x4, index by [from][to]. Locations: 0=Castro, 1=Alamo, 2=Union, 3=Chinatown.
    travel = [
        [0, 8, 19, 20],
        [8, 0, 14, 16],
        [19, 15, 0, 7],
        [22, 17, 7, 0]
    ]
    
    # Friends: 0=Emily (Alamo Square), 1=Barbara (Union Square), 2=William (Chinatown)
    # Each friend: (location, window_start, window_end, min_duration)
    friends = [
        (1, 165, 375, 105),  # Emily: Alamo Square, 11:45AM-3:15PM, 105 min
        (2, 465, 555, 60),    # Barbara: Union Square, 4:45PM-6:15PM, 60 min
        (3, 495, 600, 105)    # William: Chinatown, 5:15PM-7:00PM, 105 min
    ]
    
    # Create the solver and optimizer
    opt = Optimize()
    
    # Decision variables
    meet = [Bool(f'meet_{i}') for i in range(3)]  # Whether we meet each friend
    s = [Int(f's_{i}') for i in range(3)]          # Start time for each friend's meeting
    
    # Order variables for pairs: 
    # b0: True if Emily (0) before Barbara (1)
    # b1: True if Emily (0) before William (2)
    # b2: True if Barbara (1) before William (2)
    b0 = Bool('b0')
    b1 = Bool('b1')
    b2 = Bool('b2')
    
    # Constraints for each friend
    for i in range(3):
        loc_i, start_i, end_i, dur_i = friends[i]
        # If meeting the friend, constraints on start time
        opt.add(Implies(meet[i], s[i] >= travel[0][loc_i]))  # Travel from start location (Castro)
        opt.add(Implies(meet[i], s[i] >= start_i))            # Start after window opens
        opt.add(Implies(meet[i], s[i] + dur_i <= end_i))      # End before window closes
    
    # Constraints for pairs of friends
    # Emily (0) and Barbara (1)
    loc0, _, _, dur0 = friends[0]
    loc1, _, _, dur1 = friends[1]
    opt.add(Implies(And(meet[0], meet[1]),
                    If(b0, 
                       s[1] >= s[0] + dur0 + travel[loc0][loc1],
                       s[0] >= s[1] + dur1 + travel[loc1][loc0]
                    )))
    
    # Emily (0) and William (2)
    loc2, _, _, dur2 = friends[2]
    opt.add(Implies(And(meet[0], meet[2]),
                    If(b1,
                       s[2] >= s[0] + dur0 + travel[loc0][loc2],
                       s[0] >= s[2] + dur2 + travel[loc2][loc0]
                    )))
    
    # Barbara (1) and William (2)
    opt.add(Implies(And(meet[1], meet[2]),
                    If(b2,
                       s[2] >= s[1] + dur1 + travel[loc1][loc2],
                       s[1] >= s[2] + dur2 + travel[loc2][loc1]
                    )))
    
    # Transitivity constraints to avoid cycles when all three are met
    opt.add(Implies(And(meet[0], meet[1], meet[2]),
                   And(
                       Not(And(b0, b2, Not(b1))),  # Avoid cycle: E before B, B before W, and W before E
                       Not(And(b1, Not(b2), Not(b0)))  # Avoid cycle: E before W, W before B, and B before E
                   ))
    
    # Maximize the number of friends met
    opt.maximize(Sum([If(meet[i], 1, 0) for i in range(3)]))
    
    # Check for a solution
    if opt.check() == sat:
        model = opt.model()
        # Convert start times to time strings
        def minutes_to_time(minutes):
            total_minutes = minutes
            hours = total_minutes // 60
            minutes_remainder = total_minutes % 60
            total_hours = 9 + hours
            if total_hours >= 13:
                hour_str = total_hours - 12
                period = "PM"
            elif total_hours == 12:
                hour_str = 12
                period = "PM"
            else:
                hour_str = total_hours
                period = "AM"
            return f"{hour_str}:{minutes_remainder:02d}{period}"
        
        # Determine which friends are met and their times
        schedule = []
        friend_names = ["Emily", "Barbara", "William"]
        locations = ["Alamo Square", "Union Square", "Chinatown"]
        for i in range(3):
            if model.evaluate(meet[i]):
                start_val = model.evaluate(s[i])
                if is_int_value(start_val):
                    start_min = start_val.as_long()
                else:
                    start_min = int(str(start_val))
                start_time = minutes_to_time(start_min)
                end_min = start_min + friends[i][3]
                end_time = minutes_to_time(end_min)
                schedule.append((start_min, friend_names[i], locations[i], start_time, end_time))
        
        # Sort by start time
        schedule.sort(key=lambda x: x[0])
        
        # Print the schedule
        print("SOLUTION:")
        if not schedule:
            print("No friends were met.")
        else:
            print(f"Met {len(schedule)} friends:")
            for _, name, location, start_str, end_str in schedule:
                print(f"Meet {name} at {location} from {start_str} to {end_str}")
    else:
        print("SOLUTION:\nNo feasible schedule found.")

if __name__ == "__main__":
    main()