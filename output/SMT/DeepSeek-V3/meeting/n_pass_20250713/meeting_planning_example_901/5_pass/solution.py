from z3 import *

def solve_scheduling():
    s = Solver()

    # Define variables for each meeting's start and end times
    emily_start, emily_end = Ints('emily_start emily_end')
    helen_start, helen_end = Ints('helen_start helen_end')
    kimberly_start, kimberly_end = Ints('kimberly_start kimberly_end')
    james_start, james_end = Ints('james_start james_end')
    linda_start, linda_end = Ints('linda_start linda_end')
    paul_start, paul_end = Ints('paul_start paul_end')
    anthony_start, anthony_end = Ints('anthony_start anthony_end')
    nancy_start, nancy_end = Ints('nancy_start nancy_end')
    william_start, william_end = Ints('william_start william_end')
    margaret_start, margaret_end = Ints('margaret_start margaret_end')

    # Convert all times to minutes since midnight
    start_time = 540  # 9:00 AM

    # Time windows in minutes since midnight
    time_windows = {
        'Emily': (555, 825),    # 9:15AM-1:45PM
        'Helen': (825, 1125),   # 1:45PM-6:45PM
        'Kimberly': (1125, 1295), # 6:45PM-9:15PM
        'James': (630, 690),    # 10:30AM-11:30AM
        'Linda': (450, 1095),   # 7:30AM-7:15PM
        'Paul': (885, 1125),    # 2:45PM-6:45PM
        'Anthony': (480, 885),  # 8:00AM-2:45PM
        'Nancy': (510, 825),    # 8:30AM-1:45PM
        'William': (1050, 1230), # 5:30PM-8:30PM
        'Margaret': (975, 1095)  # 3:15PM-6:15PM
    }

    # Minimum meeting durations
    min_durations = {
        'Emily': 120,
        'Helen': 30,
        'Kimberly': 75,
        'James': 30,
        'Linda': 15,
        'Paul': 90,
        'Anthony': 105,
        'Nancy': 120,
        'William': 120,
        'Margaret': 45
    }

    # Define all meetings with their locations
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

    # Add duration and time window constraints
    for name, start, end, _ in meetings:
        s.add(end - start >= min_durations[name])
        s.add(start >= time_windows[name][0])
        s.add(end <= time_windows[name][1])

    # Travel times between locations (in minutes)
    travel_times = {
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

    # Create selection variables for each meeting
    selected = [Bool(f'selected_{name}') for name, _, _, _ in meetings]
    s.add(PbEq([(s, 1) for s in selected], 7))  # Exactly 7 meetings

    # Create ordering variables to sequence the meetings
    order = [Int(f'order_{name}') for name, _, _, _ in meetings]
    for o in order:
        s.add(o >= 1, o <= 10)  # 10 possible positions

    # All selected meetings must have unique order positions
    for i in range(len(meetings)):
        for j in range(i+1, len(meetings)):
            s.add(Implies(And(selected[i], selected[j]), order[i] != order[j]))

    # Add travel time constraints between consecutive meetings
    for i in range(len(meetings)):
        for j in range(len(meetings)):
            if i != j:
                # If both meetings are selected and i comes before j
                s.add(Implies(And(selected[i], selected[j], order[i] + 1 == order[j]),
                              meetings[j][1] >= meetings[i][2] + travel_times.get((meetings[i][3], meetings[j][3]), 0)))

    # Start from Russian Hill
    first_meeting = Or([And(selected[i], order[i] == 1) for i in range(len(meetings))])
    s.add(first_meeting)
    for i in range(len(meetings)):
        s.add(Implies(And(selected[i], order[i] == 1),
                      meetings[i][1] >= start_time + travel_times.get(('Russian Hill', meetings[i][3]), 0)))

    # Optimize to maximize the number of meetings with their full duration
    opt = Optimize()
    for name, start, end, _ in meetings:
        opt.add_soft(end - start == min_durations[name])

    # Combine the solver with the optimizer
    opt.add(s.assertions())
    if opt.check() == sat:
        m = opt.model()
        print("Feasible schedule found meeting exactly 7 people:")
        scheduled = []
        for i, (name, start, end, loc) in enumerate(meetings):
            if is_true(m[selected[i]]):
                pos = m[order[i]].as_long()
                start_time = m[start].as_long()
                end_time = m[end].as_long()
                scheduled.append((pos, name, loc, start_time, end_time))
        
        scheduled.sort()
        for pos, name, loc, start, end in scheduled:
            start_hr = start // 60
            start_min = start % 60
            end_hr = end // 60
            end_min = end % 60
            print(f"{pos}. Meet {name} at {loc} from {start_hr:02d}:{start_min:02d} to {end_hr:02d}:{end_min:02d}")
    else:
        print("No feasible schedule found meeting exactly 7 people.")

solve_scheduling()