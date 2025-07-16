from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define all time points in minutes since 9:00 AM
    # Meeting time variables
    emily_start, emily_end = Int('emily_start'), Int('emily_end')
    helen_start, helen_end = Int('helen_start'), Int('helen_end')
    kimberly_start, kimberly_end = Int('kimberly_start'), Int('kimberly_end')
    james_start, james_end = Int('james_start'), Int('james_end')
    linda_start, linda_end = Int('linda_start'), Int('linda_end')
    paul_start, paul_end = Int('paul_start'), Int('paul_end')
    anthony_start, anthony_end = Int('anthony_start'), Int('anthony_end')
    nancy_start, nancy_end = Int('nancy_start'), Int('nancy_end')
    william_start, william_end = Int('william_start'), Int('william_end')
    margaret_start, margaret_end = Int('margaret_start'), Int('margaret_end')

    # Availability windows (in minutes since 9:00 AM)
    # Emily: 9:15 AM to 1:45 PM (15 to 285)
    s.add(emily_start >= 15, emily_end <= 285)
    s.add(emily_end - emily_start >= 120)
    
    # Helen: 1:45 PM to 6:45 PM (285 to 585)
    s.add(helen_start >= 285, helen_end <= 585)
    s.add(helen_end - helen_start >= 30)
    
    # Kimberly: 6:45 PM to 9:15 PM (585 to 735)
    s.add(kimberly_start >= 585, kimberly_end <= 735)
    s.add(kimberly_end - kimberly_start >= 75)
    
    # James: 10:30 AM to 11:30 AM (90 to 150)
    s.add(james_start >= 90, james_end <= 150)
    s.add(james_end - james_start >= 30)
    
    # Linda: 7:30 AM to 7:15 PM (-90 to 615)
    s.add(linda_start >= 0, linda_end <= 615)  # Adjusted to start at 9:00 AM
    s.add(linda_end - linda_start >= 15)
    
    # Paul: 2:45 PM to 6:45 PM (345 to 585)
    s.add(paul_start >= 345, paul_end <= 585)
    s.add(paul_end - paul_start >= 90)
    
    # Anthony: 8:00 AM to 2:45 PM (-60 to 345)
    s.add(anthony_start >= 0, anthony_end <= 345)
    s.add(anthony_end - anthony_start >= 105)
    
    # Nancy: 8:30 AM to 1:45 PM (-30 to 285)
    s.add(nancy_start >= 0, nancy_end <= 285)
    s.add(nancy_end - nancy_start >= 120)
    
    # William: 5:30 PM to 8:30 PM (510 to 690)
    s.add(william_start >= 510, william_end <= 690)
    s.add(william_end - william_start >= 120)
    
    # Margaret: 3:15 PM to 6:15 PM (375 to 495)
    s.add(margaret_start >= 375, margaret_end <= 495)
    s.add(margaret_end - margaret_start >= 45)

    # Travel times from Russian Hill (minutes)
    travel = {
        'Pacific Heights': 7,
        'North Beach': 5,
        'Golden Gate Park': 21,
        'Embarcadero': 8,
        'Haight-Ashbury': 17,
        'Fisherman\'s Wharf': 7,
        'Mission District': 16,
        'Alamo Square': 15,
        'Bayview': 23,
        'Richmond District': 14
    }

    # List of all meetings with their locations
    meetings = [
        ('Emily', emily_start, emily_end, 'Pacific Heights'),
        ('Helen', helen_start, helen_end, 'North Beach'),
        ('Kimberly', kimberly_start, kimberly_end, 'Golden Gate Park'),
        ('James', james_start, james_end, 'Embarcadero'),
        ('Linda', linda_start, linda_end, 'Haight-Ashbury'),
        ('Paul', paul_start, paul_end, 'Fisherman\'s Wharf'),
        ('Anthony', anthony_start, anthony_end, 'Mission District'),
        ('Nancy', nancy_start, nancy_end, 'Alamo Square'),
        ('William', william_start, william_end, 'Bayview'),
        ('Margaret', margaret_start, margaret_end, 'Richmond District')
    ]

    # Ensure no overlapping meetings considering travel time
    for i in range(len(meetings)):
        for j in range(i+1, len(meetings)):
            name1, s1, e1, loc1 = meetings[i]
            name2, s2, e2, loc2 = meetings[j]
            # Travel time between locations (simplified to sum of individual travel times)
            travel_time = travel[loc1] + travel[loc2]
            s.add(Or(
                e1 + travel_time <= s2,  # Meeting 1 ends with enough time before Meeting 2
                e2 + travel_time <= s1   # Or Meeting 2 ends with enough time before Meeting 1
            ))

    # Check for satisfiability
    if s.check() == sat:
        m = s.model()
        print("SOLUTION:")
        
        # Convert minutes to readable time format
        def minutes_to_time(minutes):
            total_hours = 9 + minutes // 60
            hour = total_hours % 12
            if hour == 0:
                hour = 12
            minute = minutes % 60
            period = "AM" if total_hours < 12 else "PM"
            return f"{hour}:{minute:02d} {period}"
        
        # Collect all meetings with their times
        scheduled_meetings = []
        for name, start, end, loc in meetings:
            start_val = m[start].as_long()
            end_val = m[end].as_long()
            scheduled_meetings.append((
                start_val,
                f"Meet {name} at {loc} from {minutes_to_time(start_val)} to {minutes_to_time(end_val)}"
            ))
        
        # Sort meetings by start time and print
        scheduled_meetings.sort()
        for _, meeting in scheduled_meetings:
            print(meeting)
    else:
        print("No valid schedule found that meets all constraints")

solve_scheduling()