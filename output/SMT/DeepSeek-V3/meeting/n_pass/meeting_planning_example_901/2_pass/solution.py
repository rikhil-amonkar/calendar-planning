from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define variables for each meeting's start and end times (in minutes since 9:00 AM)
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

    # Convert all time windows to minutes since 9:00 AM
    # Emily: 9:15 AM to 1:45 PM (15 to 285 minutes)
    s.add(emily_start >= 15, emily_end <= 285)
    s.add(emily_end - emily_start >= 120)  # Minimum 120 minutes

    # Helen: 1:45 PM to 6:45 PM (285 to 585 minutes)
    s.add(helen_start >= 285, helen_end <= 585)
    s.add(helen_end - helen_start >= 30)  # Minimum 30 minutes

    # Kimberly: 6:45 PM to 9:15 PM (585 to 735 minutes)
    s.add(kimberly_start >= 585, kimberly_end <= 735)
    s.add(kimberly_end - kimberly_start >= 75)  # Minimum 75 minutes

    # James: 10:30 AM to 11:30 AM (90 to 150 minutes)
    s.add(james_start >= 90, james_end <= 150)
    s.add(james_end - james_start >= 30)  # Minimum 30 minutes

    # Linda: 7:30 AM to 7:15 PM (-90 to 615 minutes)
    s.add(linda_start >= -90, linda_end <= 615)
    s.add(linda_end - linda_start >= 15)  # Minimum 15 minutes

    # Paul: 2:45 PM to 6:45 PM (345 to 585 minutes)
    s.add(paul_start >= 345, paul_end <= 585)
    s.add(paul_end - paul_start >= 90)  # Minimum 90 minutes

    # Anthony: 8:00 AM to 2:45 PM (-60 to 345 minutes)
    s.add(anthony_start >= -60, anthony_end <= 345)
    s.add(anthony_end - anthony_start >= 105)  # Minimum 105 minutes

    # Nancy: 8:30 AM to 1:45 PM (-30 to 285 minutes)
    s.add(nancy_start >= -30, nancy_end <= 285)
    s.add(nancy_end - nancy_start >= 120)  # Minimum 120 minutes

    # William: 5:30 PM to 8:30 PM (510 to 690 minutes)
    s.add(william_start >= 510, william_end <= 690)
    s.add(william_end - william_start >= 120)  # Minimum 120 minutes

    # Margaret: 3:15 PM to 6:15 PM (375 to 495 minutes)
    s.add(margaret_start >= 375, margaret_end <= 495)
    s.add(margaret_end - margaret_start >= 45)  # Minimum 45 minutes

    # Define travel times from Russian Hill (starting point)
    travel_times = {
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

    # Define meetings with their locations
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

    # Ensure all meetings are after 9:00 AM (0 minutes)
    for meeting in meetings:
        s.add(meeting[1] >= 0)

    # Define no-overlap constraints considering travel times
    # For simplicity, assume you return to Russian Hill between meetings
    # and travel time is from Russian Hill to the next location
    for i in range(len(meetings)):
        for j in range(i + 1, len(meetings)):
            name1, s1, e1, loc1 = meetings[i]
            name2, s2, e2, loc2 = meetings[j]
            # Travel time from loc1 back to Russian Hill and then to loc2
            travel_time = travel_times[loc1] + travel_times[loc2]
            s.add(Or(
                e1 + travel_time <= s2,
                e2 + travel_time <= s1
            ))

    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        # Print the schedule
        print("SOLUTION:")
        for meeting in meetings:
            name, start, end, loc = meeting
            start_time = m[start].as_long()
            end_time = m[end].as_long()
            print(f"Meet {name} at {loc} from {start_time} to {end_time} minutes since 9:00 AM")
    else:
        print("No valid schedule found")

solve_scheduling()