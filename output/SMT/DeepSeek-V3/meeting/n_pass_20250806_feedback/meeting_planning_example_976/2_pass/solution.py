from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 optimizer
    opt = Optimize()

    # Define travel times (from_location, to_location) -> minutes
    travel_times = {
        ('Embarcadero', 'Bayview'): 21,
        ('Embarcadero', 'Chinatown'): 7,
        ('Embarcadero', 'Alamo Square'): 19,
        ('Embarcadero', 'Nob Hill'): 10,
        ('Embarcadero', 'Presidio'): 20,
        ('Embarcadero', 'Union Square'): 10,
        ('Embarcadero', 'The Castro'): 25,
        ('Embarcadero', 'North Beach'): 5,
        ('Embarcadero', 'Fisherman\'s Wharf'): 6,
        ('Embarcadero', 'Marina District'): 12,
        ('Bayview', 'Embarcadero'): 19,
        ('Bayview', 'Chinatown'): 19,
        ('Bayview', 'Alamo Square'): 16,
        ('Bayview', 'Nob Hill'): 20,
        ('Bayview', 'Presidio'): 32,
        ('Bayview', 'Union Square'): 18,
        ('Bayview', 'The Castro'): 19,
        ('Bayview', 'North Beach'): 22,
        ('Bayview', 'Fisherman\'s Wharf'): 25,
        ('Bayview', 'Marina District'): 27,
        ('Chinatown', 'Embarcadero'): 5,
        ('Chinatown', 'Bayview'): 20,
        ('Chinatown', 'Alamo Square'): 17,
        ('Chinatown', 'Nob Hill'): 9,
        ('Chinatown', 'Presidio'): 19,
        ('Chinatown', 'Union Square'): 7,
        ('Chinatown', 'The Castro'): 22,
        ('Chinatown', 'North Beach'): 3,
        ('Chinatown', 'Fisherman\'s Wharf'): 8,
        ('Chinatown', 'Marina District'): 12,
        ('Alamo Square', 'Embarcadero'): 16,
        ('Alamo Square', 'Bayview'): 16,
        ('Alamo Square', 'Chinatown'): 15,
        ('Alamo Square', 'Nob Hill'): 11,
        ('Alamo Square', 'Presidio'): 17,
        ('Alamo Square', 'Union Square'): 14,
        ('Alamo Square', 'The Castro'): 8,
        ('Alamo Square', 'North Beach'): 15,
        ('Alamo Square', 'Fisherman\'s Wharf'): 19,
        ('Alamo Square', 'Marina District'): 15,
        ('Nob Hill', 'Embarcadero'): 9,
        ('Nob Hill', 'Bayview'): 19,
        ('Nob Hill', 'Chinatown'): 6,
        ('Nob Hill', 'Alamo Square'): 11,
        ('Nob Hill', 'Presidio'): 17,
        ('Nob Hill', 'Union Square'): 7,
        ('Nob Hill', 'The Castro'): 17,
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'Fisherman\'s Wharf'): 10,
        ('Nob Hill', 'Marina District'): 11,
        ('Presidio', 'Embarcadero'): 20,
        ('Presidio', 'Bayview'): 31,
        ('Presidio', 'Chinatown'): 21,
        ('Presidio', 'Alamo Square'): 19,
        ('Presidio', 'Nob Hill'): 18,
        ('Presidio', 'Union Square'): 22,
        ('Presidio', 'The Castro'): 21,
        ('Presidio', 'North Beach'): 18,
        ('Presidio', 'Fisherman\'s Wharf'): 19,
        ('Presidio', 'Marina District'): 11,
        ('Union Square', 'Embarcadero'): 11,
        ('Union Square', 'Bayview'): 15,
        ('Union Square', 'Chinatown'): 7,
        ('Union Square', 'Alamo Square'): 15,
        ('Union Square', 'Nob Hill'): 9,
        ('Union Square', 'Presidio'): 24,
        ('Union Square', 'The Castro'): 17,
        ('Union Square', 'North Beach'): 10,
        ('Union Square', 'Fisherman\'s Wharf'): 15,
        ('Union Square', 'Marina District'): 18,
        ('The Castro', 'Embarcadero'): 22,
        ('The Castro', 'Bayview'): 19,
        ('The Castro', 'Chinatown'): 22,
        ('The Castro', 'Alamo Square'): 8,
        ('The Castro', 'Nob Hill'): 16,
        ('The Castro', 'Presidio'): 20,
        ('The Castro', 'Union Square'): 19,
        ('The Castro', 'North Beach'): 20,
        ('The Castro', 'Fisherman\'s Wharf'): 24,
        ('The Castro', 'Marina District'): 21,
        ('North Beach', 'Embarcadero'): 6,
        ('North Beach', 'Bayview'): 25,
        ('North Beach', 'Chinatown'): 6,
        ('North Beach', 'Alamo Square'): 16,
        ('North Beach', 'Nob Hill'): 7,
        ('North Beach', 'Presidio'): 17,
        ('North Beach', 'Union Square'): 7,
        ('North Beach', 'The Castro'): 23,
        ('North Beach', 'Fisherman\'s Wharf'): 5,
        ('North Beach', 'Marina District'): 9,
        ('Fisherman\'s Wharf', 'Embarcadero'): 8,
        ('Fisherman\'s Wharf', 'Bayview'): 26,
        ('Fisherman\'s Wharf', 'Chinatown'): 12,
        ('Fisherman\'s Wharf', 'Alamo Square'): 21,
        ('Fisherman\'s Wharf', 'Nob Hill'): 11,
        ('Fisherman\'s Wharf', 'Presidio'): 17,
        ('Fisherman\'s Wharf', 'Union Square'): 13,
        ('Fisherman\'s Wharf', 'The Castro'): 27,
        ('Fisherman\'s Wharf', 'North Beach'): 6,
        ('Fisherman\'s Wharf', 'Marina District'): 9,
        ('Marina District', 'Embarcadero'): 14,
        ('Marina District', 'Bayview'): 27,
        ('Marina District', 'Chinatown'): 15,
        ('Marina District', 'Alamo Square'): 15,
        ('Marina District', 'Nob Hill'): 12,
        ('Marina District', 'Presidio'): 10,
        ('Marina District', 'Union Square'): 16,
        ('Marina District', 'The Castro'): 22,
        ('Marina District', 'North Beach'): 11,
        ('Marina District', 'Fisherman\'s Wharf'): 10,
    }

    # Friends data: name, location, available start, available end, min duration (minutes)
    friends = [
        ("Matthew", "Bayview", (19, 15), (22, 0), 120),
        ("Karen", "Chinatown", (19, 15), (21, 15), 90),
        ("Sarah", "Alamo Square", (20, 0), (21, 45), 105),
        ("Jessica", "Nob Hill", (16, 30), (18, 45), 120),
        ("Stephanie", "Presidio", (7, 30), (10, 15), 60),
        ("Mary", "Union Square", (16, 45), (21, 30), 60),
        ("Charles", "The Castro", (16, 30), (22, 0), 105),
        ("Nancy", "North Beach", (14, 45), (20, 0), 15),
        ("Thomas", "Fisherman's Wharf", (13, 30), (19, 0), 30),
        ("Brian", "Marina District", (12, 15), (18, 0), 60),
    ]

    # Convert time to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(h, m):
        return h * 60 + m

    start_time_min = time_to_minutes(9, 0)  # 9:00 AM

    # Create variables for each friend's meeting start and end times
    meet_vars = []
    for name, loc, (sh, sm), (eh, em), dur in friends:
        start_var = Int(f'start_{name}')
        end_var = Int(f'end_{name}')
        meet_vars.append((name, loc, start_var, end_var, dur, time_to_minutes(sh, sm), time_to_minutes(eh, em)))

    # Constraints for each meeting
    for name, loc, start, end, dur, s_min, e_min in meet_vars:
        opt.add(start >= s_min - start_time_min)
        opt.add(end <= e_min - start_time_min)
        opt.add(end >= start + dur)
        opt.add(start >= 0)  # Ensure start time is after 9:00 AM

    # Sequence constraints: order of meetings and travel times
    # We'll prioritize meeting friends with the earliest available times first
    # and ensure travel times are respected between consecutive meetings
    order = [
        ("Stephanie", "Presidio"),
        ("Brian", "Marina District"),
        ("Thomas", "Fisherman's Wharf"),
        ("Nancy", "North Beach"),
        ("Jessica", "Nob Hill"),
        ("Mary", "Union Square"),
        ("Charles", "The Castro"),
        ("Sarah", "Alamo Square"),
        ("Karen", "Chinatown"),
        ("Matthew", "Bayview"),
    ]

    # Get the start and end variables for each in the order
    ordered_vars = []
    for name, loc in order:
        for v in meet_vars:
            if v[0] == name and v[1] == loc:
                ordered_vars.append(v)
                break

    # Add travel time constraints between consecutive meetings
    for i in range(len(ordered_vars) - 1):
        prev_name, prev_loc, prev_start, prev_end, _, _, _ = ordered_vars[i]
        next_name, next_loc, next_start, next_end, _, _, _ = ordered_vars[i + 1]
        travel_key = (prev_loc, next_loc)
        if travel_key in travel_times:
            travel_time = travel_times[travel_key]
            opt.add(next_start >= prev_end + travel_time)
        else:
            # Assume maximum travel time if not found (though ideally, all should be present)
            opt.add(next_start >= prev_end + 60)  # arbitrary large value

    # Also, the first meeting must start after arriving at Embarcadero at 9:00 AM (time 0)
    first_start = ordered_vars[0][2]
    opt.add(first_start >= 0)

    # Maximize the total meeting time
    total_meeting_time = sum([end - start for _, _, start, end, _, _, _ in ordered_vars])
    opt.maximize(total_meeting_time)

    # Check if a solution exists
    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        for name, loc, start_var, end_var, _, _, _ in ordered_vars:
            start_val = m.evaluate(start_var).as_long()
            end_val = m.evaluate(end_var).as_long()
            start_h = (start_time_min + start_val) // 60
            start_m = (start_time_min + start_val) % 60
            end_h = (start_time_min + end_val) // 60
            end_m = (start_time_min + end_val) % 60
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": f"{start_h:02d}:{start_m:02d}",
                "end_time": f"{end_h:02d}:{end_m:02d}"
            })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: (int(x['start_time'][:2]), int(x['start_time'][3:5])))
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No feasible schedule found.")

solve_scheduling_problem()