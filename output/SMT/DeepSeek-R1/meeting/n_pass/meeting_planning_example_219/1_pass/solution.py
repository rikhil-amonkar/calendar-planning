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
    loc = [1, 2, 3]  # Location indices for each friend
    start_window = [165, 465, 495]  # Start times in minutes from 9:00 AM
    end_window = [375, 555, 600]    # End times in minutes from 9:00 AM
    duration = [105, 60, 105]       # Minimum meeting durations in minutes
    
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
        # If meeting the friend, constraints on start time
        opt.add(Implies(meet[i], s[i] >= travel[0][loc[i]]))  # Travel from start location
        opt.add(Implies(meet[i], s[i] >= start_window[i]))     # Start after window opens
        opt.add(Implies(meet[i], s[i] + duration[i] <= end_window[i]))  # End before window closes
    
    # Constraints for pairs of friends
    # Emily (0) and Barbara (1)
    opt.add(Implies(And(meet[0], meet[1]),
                    If(b0, 
                       s[1] >= s[0] + duration[0] + travel[loc[0]][loc[1]],
                       s[0] >= s[1] + duration[1] + travel[loc[1]][loc[0]]
                    )))
    
    # Emily (0) and William (2)
    opt.add(Implies(And(meet[0], meet[2]),
                    If(b1,
                       s[2] >= s[0] + duration[0] + travel[loc[0]][loc[2]],
                       s[0] >= s[2] + duration[2] + travel[loc[2]][loc[0]]
                    )))
    
    # Barbara (1) and William (2)
    opt.add(Implies(And(meet[1], meet[2]),
                    If(b2,
                       s[2] >= s[1] + duration[1] + travel[loc[1]][loc[2]],
                       s[1] >= s[2] + duration[2] + travel[loc[2]][loc[1]]
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
            total_minutes = int(str(model.evaluate(minutes)))
            hours = total_minutes // 60
            minutes = total_minutes % 60
            am_pm = "AM" if hours < 12 else "PM"
            hours12 = hours if hours <= 12 else hours - 12
            return f"{hours12}:{minutes:02d}{am_pm}"
        
        # Determine which friends are met and their times
        schedule = []
        friend_names = ["Emily", "Barbara", "William"]
        locations = ["Alamo Square", "Union Square", "Chinatown"]
        for i in range(3):
            if model.evaluate(meet[i]):
                start_val = model.evaluate(s[i])
                start_time = minutes_to_time(s[i])
                end_time = minutes_to_time(s[i] + duration[i])
                schedule.append((start_val, friend_names[i], locations[i], start_time, end_time))
        
        # Sort by start time
        schedule.sort(key=lambda x: int(str(x[0])))
        
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