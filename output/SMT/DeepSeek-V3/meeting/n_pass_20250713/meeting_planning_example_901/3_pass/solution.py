from z3 import *

def solve_scheduling():
    s = Solver()

    # Define variables for each meeting's start and end times
    # Emily at Pacific Heights: 9:15AM to 1:45PM, min 120 mins
    emily_start = Int('emily_start')
    emily_end = Int('emily_end')
    # Helen at North Beach: 1:45PM to 6:45PM, min 30 mins
    helen_start = Int('helen_start')
    helen_end = Int('helen_end')
    # Kimberly at Golden Gate Park: 6:45PM to 9:15PM, min 75 mins
    kimberly_start = Int('kimberly_start')
    kimberly_end = Int('kimberly_end')
    # James at Embarcadero: 10:30AM to 11:30AM, min 30 mins
    james_start = Int('james_start')
    james_end = Int('james_end')
    # Linda at Haight-Ashbury: 7:30AM to 7:15PM, min 15 mins
    linda_start = Int('linda_start')
    linda_end = Int('linda_end')
    # Paul at Fisherman's Wharf: 2:45PM to 6:45PM, min 90 mins
    paul_start = Int('paul_start')
    paul_end = Int('paul_end')
    # Anthony at Mission District: 8:00AM to 2:45PM, min 105 mins
    anthony_start = Int('anthony_start')
    anthony_end = Int('anthony_end')
    # Nancy at Alamo Square: 8:30AM to 1:45PM, min 120 mins
    nancy_start = Int('nancy_start')
    nancy_end = Int('nancy_end')
    # William at Bayview: 5:30PM to 8:30PM, min 120 mins
    william_start = Int('william_start')
    william_end = Int('william_end')
    # Margaret at Richmond District: 3:15PM to 6:15PM, min 45 mins
    margaret_start = Int('margaret_start')
    margaret_end = Int('margaret_end')

    # Convert all times to minutes since midnight
    # Russian Hill start time: 9:00 AM (540)
    start_time = 540

    # Time windows (in minutes since midnight)
    emily_min = 555  # 9:15 AM
    emily_max = 825  # 1:45 PM
    helen_min = 825  # 1:45 PM
    helen_max = 1125 # 6:45 PM
    kimberly_min = 1125 # 6:45 PM
    kimberly_max = 1295 # 9:15 PM
    james_min = 630  # 10:30 AM
    james_max = 690  # 11:30 AM
    linda_min = 450  # 7:30 AM
    linda_max = 1095 # 7:15 PM
    paul_min = 885  # 2:45 PM
    paul_max = 1125 # 6:45 PM
    anthony_min = 480 # 8:00 AM
    anthony_max = 885 # 2:45 PM
    nancy_min = 510 # 8:30 AM
    nancy_max = 825 # 1:45 PM
    william_min = 1050 # 5:30 PM
    william_max = 1230 # 8:30 PM
    margaret_min = 975 # 3:15 PM
    margaret_max = 1095 # 6:15 PM

    # Meeting duration constraints
    s.add(emily_end - emily_start >= 120)
    s.add(helen_end - helen_start >= 30)
    s.add(kimberly_end - kimberly_start >= 75)
    s.add(james_end - james_start >= 30)
    s.add(linda_end - linda_start >= 15)
    s.add(paul_end - paul_start >= 90)
    s.add(anthony_end - anthony_start >= 105)
    s.add(nancy_end - nancy_start >= 120)
    s.add(william_end - william_start >= 120)
    s.add(margaret_end - margaret_start >= 45)

    # Time window constraints
    s.add(emily_start >= emily_min, emily_end <= emily_max)
    s.add(helen_start >= helen_min, helen_end <= helen_max)
    s.add(kimberly_start >= kimberly_min, kimberly_end <= kimberly_max)
    s.add(james_start >= james_min, james_end <= james_max)
    s.add(linda_start >= linda_min, linda_end <= linda_max)
    s.add(paul_start >= paul_min, paul_end <= paul_max)
    s.add(anthony_start >= anthony_min, anthony_end <= anthony_max)
    s.add(nancy_start >= nancy_min, nancy_end <= nancy_max)
    s.add(william_start >= william_min, william_end <= william_max)
    s.add(margaret_start >= margaret_min, margaret_end <= margaret_max)

    # Define travel times (in minutes)
    travel = {
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'Pacific Heights'): 7,
        ('Russian Hill', 'North Beach'): 5,
        ('Russian Hill', 'Golden Gate Park'): 21,
        ('Russian Hill', 'Embarcadero'): 8,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('Russian Hill', 'Fisherman\'s Wharf'): 7,
        ('Russian Hill', 'Mission District'): 16,
        ('Russian Hill', 'Bayview'): 23,
        ('Russian Hill', 'Richmond District'): 14,
        ('Alamo Square', 'Pacific Heights'): 10,
        ('Alamo Square', 'North Beach'): 16,
        ('Alamo Square', 'Golden Gate Park'): 9,
        ('Alamo Square', 'Embarcadero'): 19,
        ('Alamo Square', 'Haight-Ashbury'): 5,
        ('Alamo Square', 'Fisherman\'s Wharf'): 21,
        ('Alamo Square', 'Mission District'): 10,
        ('Alamo Square', 'Bayview'): 16,
        ('Alamo Square', 'Richmond District'): 11,
        ('Pacific Heights', 'North Beach'): 9,
        ('Pacific Heights', 'Golden Gate Park'): 15,
        ('Pacific Heights', 'Embarcadero'): 10,
        ('Pacific Heights', 'Haight-Ashbury'): 11,
        ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
        ('Pacific Heights', 'Mission District'): 15,
        ('Pacific Heights', 'Bayview'): 22,
        ('Pacific Heights', 'Richmond District'): 12,
        ('North Beach', 'Golden Gate Park'): 22,
        ('North Beach', 'Embarcadero'): 6,
        ('North Beach', 'Haight-Ashbury'): 18,
        ('North Beach', 'Fisherman\'s Wharf'): 5,
        ('North Beach', 'Mission District'): 18,
        ('North Beach', 'Bayview'): 25,
        ('North Beach', 'Richmond District'): 18,
        ('Golden Gate Park', 'Embarcadero'): 25,
        ('Golden Gate Park', 'Haight-Ashbury'): 7,
        ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
        ('Golden Gate Park', 'Mission District'): 17,
        ('Golden Gate Park', 'Bayview'): 23,
        ('Golden Gate Park', 'Richmond District'): 7,
        ('Embarcadero', 'Haight-Ashbury'): 21,
        ('Embarcadero', 'Fisherman\'s Wharf'): 6,
        ('Embarcadero', 'Mission District'): 20,
        ('Embarcadero', 'Bayview'): 21,
        ('Embarcadero', 'Richmond District'): 21,
        ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Haight-Ashbury', 'Richmond District'): 10,
        ('Fisherman\'s Wharf', 'Mission District'): 22,
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Fisherman\'s Wharf', 'Richmond District'): 18,
        ('Mission District', 'Bayview'): 14,
        ('Mission District', 'Richmond District'): 20,
        ('Bayview', 'Richmond District'): 27
    }

    # Define a list to hold all meetings and their locations
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

    # To meet exactly 7 people, we need to select 7 out of 10 meetings
    # We'll use pseudo-boolean constraints to ensure exactly 7 meetings are selected
    selected = [Bool(f'selected_{name}') for name, _, _, _ in meetings]
    s.add(PbEq([(selected[i], 1) for i in range(len(meetings))], 7))

    # Define the order of meetings and enforce travel times
    # For simplicity, we'll assume a fixed order and adjust constraints accordingly
    # This is a heuristic and may not find the optimal schedule
    # Start at Russian Hill at 540
    last_location = 'Russian Hill'
    last_end = start_time

    # Iterate over meetings in a fixed order
    for i, (name, start, end, loc) in enumerate(meetings):
        # If this meeting is selected, enforce travel time and update last_end
        s.add(Implies(selected[i], start >= last_end + travel.get((last_location, loc), 0)))
        s.add(Implies(selected[i], last_end == end))
        s.add(Implies(selected[i], last_location == loc))

    # Check if the constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        print("Feasible schedule found:")
        scheduled_meetings = []
        for i, (name, start, end, loc) in enumerate(meetings):
            if is_true(m[selected[i]]):
                start_time = m[start].as_long()
                end_time = m[end].as_long()
                start_hour = start_time // 60
                start_min = start_time % 60
                end_hour = end_time // 60
                end_min = end_time % 60
                scheduled_meetings.append((name, loc, start_hour, start_min, end_hour, end_min))
        
        # Sort meetings by start time
        scheduled_meetings.sort(key=lambda x: (x[2], x[3]))
        for name, loc, sh, sm, eh, em in scheduled_meetings:
            print(f"Meet {name} at {loc} from {sh:02d}:{sm:02d} to {eh:02d}:{em:02d}")
    else:
        print("No feasible schedule found.")

solve_scheduling()