from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Define variables for meeting times
    joseph_start = Int('joseph_start')
    joseph_end = Int('joseph_end')
    nancy_start = Int('nancy_start')
    nancy_end = Int('nancy_end')
    jason_start = Int('jason_start')
    jason_end = Int('jason_end')
    jeffrey_start = Int('jeffrey_start')
    jeffrey_end = Int('jeffrey_end')

    # Convert times to minutes since midnight
    arrival_time = 9 * 60  # 9:00 AM (540 minutes)

    # Availability windows
    joseph_available = (8*60 + 30, 19*60 + 15)  # 8:30AM-7:15PM
    nancy_available = (11*60, 16*60)            # 11AM-4PM
    jason_available = (16*60 + 45, 21*60 + 45)  # 4:45PM-9:45PM
    jeffrey_available = (10*60 + 30, 15*60 + 45) # 10:30AM-3:45PM

    # Minimum durations
    durations = {
        'joseph': 60,
        'nancy': 90,
        'jason': 15,
        'jeffrey': 45
    }

    # Travel times between locations (in minutes)
    travel_times = {
        ('Bayview', 'Russian Hill'): 23,
        ('Bayview', 'Alamo Square'): 16,
        ('Bayview', 'North Beach'): 21,
        ('Bayview', 'Financial District'): 19,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'North Beach'): 5,
        ('Russian Hill', 'Financial District'): 11,
        ('Alamo Square', 'Russian Hill'): 13,
        ('Alamo Square', 'North Beach'): 15,
        ('Alamo Square', 'Financial District'): 17,
        ('North Beach', 'Russian Hill'): 4,
        ('North Beach', 'Alamo Square'): 16,
        ('North Beach', 'Financial District'): 8,
        ('Financial District', 'Russian Hill'): 10,
        ('Financial District', 'Alamo Square'): 17,
        ('Financial District', 'North Beach'): 7,
    }

    # Meeting constraints
    meetings = [
        ('joseph', joseph_start, joseph_end, joseph_available, 'Russian Hill'),
        ('nancy', nancy_start, nancy_end, nancy_available, 'Alamo Square'),
        ('jason', jason_start, jason_end, jason_available, 'North Beach'),
        ('jeffrey', jeffrey_start, jeffrey_end, jeffrey_available, 'Financial District')
    ]

    # Add basic constraints for each meeting
    for name, start, end, (avail_start, avail_end), location in meetings:
        s.add(start >= avail_start)
        s.add(end <= avail_end)
        s.add(end - start >= durations[name])
        s.add(start >= 0)
        s.add(end > start)

    # Variables to track which meetings are scheduled
    scheduled = {name: Int(f'scheduled_{name}') for name in ['joseph', 'nancy', 'jason', 'jeffrey']}
    for name in scheduled:
        s.add(Or(scheduled[name] == 0, scheduled[name] == 1))

    # Link scheduled variables to meeting times
    for name, start, end, _, _ in meetings:
        s.add(Implies(scheduled[name] == 1, And(start >= 0, end > start)))

    # Ensure first meeting starts after arrival + travel time
    for name, start, _, _, location in meetings:
        s.add(Implies(scheduled[name] == 1, start >= arrival_time + travel_times[('Bayview', location)]))

    # Ordering constraints between meetings
    for i, (name1, start1, end1, _, loc1) in enumerate(meetings):
        for j, (name2, start2, _, _, loc2) in enumerate(meetings):
            if i != j:
                # If both meetings are scheduled, ensure proper ordering
                s.add(Implies(
                    And(scheduled[name1] == 1, scheduled[name2] == 1),
                    Or(
                        end1 + travel_times[(loc1, loc2)] <= start2,  # Meeting1 before Meeting2
                        end2 + travel_times[(loc2, loc1)] <= start1   # Meeting2 before Meeting1
                    )
                ))

    # Objective: maximize number of meetings
    total_met = sum(scheduled.values())
    s.maximize(total_met)

    # Solve and print results
    if s.check() == sat:
        m = s.model()
        print("Optimal schedule found:")
        print(f"Total friends met: {m.evaluate(total_met)}")
        
        for name, start, end, _, _ in meetings:
            if m.evaluate(scheduled[name]) == 1:
                start_time = m.evaluate(start)
                end_time = m.evaluate(end)
                print(f"{name.capitalize()}: {start_time//60:02d}:{start_time%60:02d} to {end_time//60:02d}:{end_time%60:02d}")
            else:
                print(f"{name.capitalize()}: Not scheduled")
    else:
        print("No feasible schedule found")

solve_scheduling()