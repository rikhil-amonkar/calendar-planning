from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Optimize()

    # Define variables for each meeting's start and end times
    joseph_start = Int('joseph_start')
    joseph_end = Int('joseph_end')
    nancy_start = Int('nancy_start')
    nancy_end = Int('nancy_end')
    jason_start = Int('jason_start')
    jason_end = Int('jason_end')
    jeffrey_start = Int('jeffrey_start')
    jeffrey_end = Int('jeffrey_end')

    # Convert all times to minutes since midnight
    arrival_time = 9 * 60  # 9:00 AM (540 minutes)

    # Friends' availability windows in minutes since midnight
    joseph_available_start = 8 * 60 + 30  # 8:30 AM (510 minutes)
    joseph_available_end = 19 * 60 + 15   # 7:15 PM (1155 minutes)
    nancy_available_start = 11 * 60       # 11:00 AM (660 minutes)
    nancy_available_end = 16 * 60         # 4:00 PM (960 minutes)
    jason_available_start = 16 * 60 + 45  # 4:45 PM (1005 minutes)
    jason_available_end = 21 * 60 + 45    # 9:45 PM (1305 minutes)
    jeffrey_available_start = 10 * 60 + 30 # 10:30 AM (630 minutes)
    jeffrey_available_end = 15 * 60 + 45  # 3:45 PM (945 minutes)

    # Minimum meeting durations in minutes
    joseph_min_duration = 60
    nancy_min_duration = 90
    jason_min_duration = 15
    jeffrey_min_duration = 45

    # Constraints for each meeting's duration and availability
    s.add(joseph_start >= joseph_available_start)
    s.add(joseph_end <= joseph_available_end)
    s.add(joseph_end - joseph_start >= joseph_min_duration)

    s.add(nancy_start >= nancy_available_start)
    s.add(nancy_end <= nancy_available_end)
    s.add(nancy_end - nancy_start >= nancy_min_duration)

    s.add(jason_start >= jason_available_start)
    s.add(jason_end <= jason_available_end)
    s.add(jason_end - jason_start >= jason_min_duration)

    s.add(jeffrey_start >= jeffrey_available_start)
    s.add(jeffrey_end <= jeffrey_available_end)
    s.add(jeffrey_end - jeffrey_start >= jeffrey_min_duration)

    # Variables to indicate whether each friend is met
    meet_joseph = Int('meet_joseph')
    meet_nancy = Int('meet_nancy')
    meet_jason = Int('meet_jason')
    meet_jeffrey = Int('meet_jeffrey')

    # These variables are 1 if the friend is met, 0 otherwise
    s.add(Or(meet_joseph == 0, meet_joseph == 1))
    s.add(Or(meet_nancy == 0, meet_nancy == 1))
    s.add(Or(meet_jason == 0, meet_jason == 1))
    s.add(Or(meet_jeffrey == 0, meet_jeffrey == 1))

    # If a friend is met, their meeting must be scheduled
    s.add(Implies(meet_joseph == 1, And(joseph_start >= 0, joseph_end > joseph_start)))
    s.add(Implies(meet_nancy == 1, And(nancy_start >= 0, nancy_end > nancy_start)))
    s.add(Implies(meet_jason == 1, And(jason_start >= 0, jason_end > jason_start)))
    s.add(Implies(meet_jeffrey == 1, And(jeffrey_start >= 0, jeffrey_end > jeffrey_start)))

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

    # Ensure the first meeting starts after arrival_time + travel time from Bayview
    s.add(Implies(meet_joseph == 1, joseph_start >= arrival_time + travel_times[('Bayview', 'Russian Hill')]))
    s.add(Implies(meet_nancy == 1, nancy_start >= arrival_time + travel_times[('Bayview', 'Alamo Square')]))
    s.add(Implies(meet_jason == 1, jason_start >= arrival_time + travel_times[('Bayview', 'North Beach')]))
    s.add(Implies(meet_jeffrey == 1, jeffrey_start >= arrival_time + travel_times[('Bayview', 'Financial District')]))

    # Ensure that if two meetings are scheduled, the second starts after the first ends plus travel time
    # Joseph before Nancy
    s.add(Implies(And(meet_joseph == 1, meet_nancy == 1), 
                  joseph_end + travel_times[('Russian Hill', 'Alamo Square')] <= nancy_start))
    # Joseph before Jason
    s.add(Implies(And(meet_joseph == 1, meet_jason == 1), 
                  joseph_end + travel_times[('Russian Hill', 'North Beach')] <= jason_start))
    # Joseph before Jeffrey
    s.add(Implies(And(meet_joseph == 1, meet_jeffrey == 1), 
                  joseph_end + travel_times[('Russian Hill', 'Financial District')] <= jeffrey_start))
    # Nancy before Jason
    s.add(Implies(And(meet_nancy == 1, meet_jason == 1), 
                  nancy_end + travel_times[('Alamo Square', 'North Beach')] <= jason_start))
    # Nancy before Jeffrey
    s.add(Implies(And(meet_nancy == 1, meet_jeffrey == 1), 
                  nancy_end + travel_times[('Alamo Square', 'Financial District')] <= jeffrey_start))
    # Jason before Jeffrey
    s.add(Implies(And(meet_jason == 1, meet_jeffrey == 1), 
                  jason_end + travel_times[('North Beach', 'Financial District')] <= jeffrey_start))

    # Objective: maximize the number of friends met
    total_met = meet_joseph + meet_nancy + meet_jason + meet_jeffrey
    s.maximize(total_met)

    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        print("Optimal schedule found. Friends met:", m.evaluate(total_met))
        print("Joseph:", m.evaluate(meet_joseph))
        if m.evaluate(meet_joseph) == 1:
            print("  Start:", m.evaluate(joseph_start), "End:", m.evaluate(joseph_end))
        print("Nancy:", m.evaluate(meet_nancy))
        if m.evaluate(meet_nancy) == 1:
            print("  Start:", m.evaluate(nancy_start), "End:", m.evaluate(nancy_end))
        print("Jason:", m.evaluate(meet_jason))
        if m.evaluate(meet_jason) == 1:
            print("  Start:", m.evaluate(jason_start), "End:", m.evaluate(jason_end))
        print("Jeffrey:", m.evaluate(meet_jeffrey))
        if m.evaluate(meet_jeffrey) == 1:
            print("  Start:", m.evaluate(jeffrey_start), "End:", m.evaluate(jeffrey_end))
    else:
        print("No feasible schedule found.")

solve_scheduling()