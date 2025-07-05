from z3 import *

def solve_scheduling():
    s = Solver()

    # Define variables for meeting times
    ronald_start = Int('ronald_start')
    ronald_end = Int('ronald_end')
    sarah_start = Int('sarah_start')
    sarah_end = Int('sarah_end')
    helen_start = Int('helen_start')
    helen_end = Int('helen_end')
    joshua_start = Int('joshua_start')
    joshua_end = Int('joshua_end')
    margaret_start = Int('margaret_start')
    margaret_end = Int('margaret_end')

    # Convert times to minutes since midnight
    # Starting at Pacific Heights at 9:00 AM (540)
    # Sarah: 7:15 AM (435) to 9:30 AM (570)
    # Ronald: 10:00 AM (600) to 5:00 PM (1020)
    # Helen: 1:30 PM (810) to 5:00 PM (1020)
    # Joshua: 2:15 PM (855) to 7:30 PM (1290)
    # Margaret: 10:15 AM (615) to 10:00 PM (1320)

    # Meeting duration constraints
    s.add(sarah_end - sarah_start >= 45)
    s.add(ronald_end - ronald_start >= 105)
    s.add(helen_end - helen_start >= 120)
    s.add(joshua_end - joshua_start >= 90)
    s.add(margaret_end - margaret_start >= 60)

    # Time window constraints
    s.add(sarah_start >= 435, sarah_end <= 570)
    s.add(ronald_start >= 600, ronald_end <= 1020)
    s.add(helen_start >= 810, helen_end <= 1020)
    s.add(joshua_start >= 855, joshua_end <= 1290)
    s.add(margaret_start >= 615, margaret_end <= 1320)

    # Travel times (in minutes)
    # From Pacific Heights to Russian Hill: 7
    # Russian Hill to Nob Hill: 5
    # Nob Hill to The Castro: 17
    # The Castro to Sunset District: 17
    # Sunset District to Haight-Ashbury: 15

    # Variables to track which friend is excluded
    exclude = [Bool(f'exclude_{name}') for name in ['sarah', 'ronald', 'helen', 'joshua', 'margaret']]
    s.add(Sum([If(e, 1, 0) for e in exclude]) == 1)  # Exactly one excluded

    # Possible meeting sequences
    sequences = [
        ['sarah', 'ronald', 'helen', 'joshua'],
        ['sarah', 'ronald', 'helen', 'margaret'],
        ['sarah', 'ronald', 'joshua', 'margaret'],
        ['sarah', 'helen', 'joshua', 'margaret'],
        ['ronald', 'helen', 'joshua', 'margaret']
    ]

    # Try each possible sequence
    for seq in sequences:
        # Reset solver for each sequence attempt
        temp_s = Solver()
        temp_s.add(s.assertions())

        # Add sequence-specific constraints
        prev_end = 540  # Start at Pacific Heights at 9:00 AM (540)
        for i in range(len(seq)-1):
            current = seq[i]
            next_friend = seq[i+1]
            
            # Add travel time between current and next
            travel_time = {
                ('sarah', 'ronald'): 5,
                ('ronald', 'helen'): 17,
                ('ronald', 'joshua'): 25,
                ('ronald', 'margaret'): 13,
                ('helen', 'joshua'): 17,
                ('helen', 'margaret'): 6,
                ('joshua', 'margaret'): 15
            }.get((current, next_friend), 0)
            
            # Get start/end variables
            start_var = globals()[f'{current}_start']
            end_var = globals()[f'{current}_end']
            next_start_var = globals()[f'{next_friend}_start']
            
            temp_s.add(start_var >= prev_end)
            temp_s.add(next_start_var >= end_var + travel_time)
            prev_end = end_var + travel_time

        # Set excluded friends
        excluded = [name for name in ['sarah', 'ronald', 'helen', 'joshua', 'margaret'] if name not in seq]
        for name in excluded:
            temp_s.add(globals()[f'exclude_{name}'] == True)
            temp_s.add(globals()[f'{name}_start'] == 0)
            temp_s.add(globals()[f'{name}_end'] == 0)

        if temp_s.check() == sat:
            m = temp_s.model()
            print("SOLUTION:")
            for name in seq:
                start = m[globals()[f'{name}_start']]
                end = m[globals()[f'{name}_end']]
                print(f"Meet {name.capitalize()} at {name} from {start} to {end}")
            return

    print("No feasible schedule found.")

solve_scheduling()