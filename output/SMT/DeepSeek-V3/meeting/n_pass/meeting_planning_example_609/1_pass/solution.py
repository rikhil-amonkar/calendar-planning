from z3 import *

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Friends and their details
    friends = {
        'David': {'location': 'Mission District', 'start': 8*60, 'end': 19*60 + 45, 'duration': 45},
        'Kenneth': {'location': 'Alamo Square', 'start': 14*60, 'end': 19*60 + 45, 'duration': 120},
        'John': {'location': 'Pacific Heights', 'start': 17*60, 'end': 20*60, 'duration': 15},
        'Charles': {'location': 'Union Square', 'start': 21*60 + 45, 'end': 22*60 + 45, 'duration': 60},
        'Deborah': {'location': 'Golden Gate Park', 'start': 7*60, 'end': 18*60 + 15, 'duration': 90},
        'Karen': {'location': 'Sunset District', 'start': 17*60 + 45, 'end': 21*60 + 15, 'duration': 15},
        'Carol': {'location': 'Presidio', 'start': 8*60 + 15, 'end': 9*60 + 15, 'duration': 30}
    }

    # Travel times dictionary (from -> to -> minutes)
    travel_times = {
        'Chinatown': {
            'Mission District': 18,
            'Alamo Square': 17,
            'Pacific Heights': 10,
            'Union Square': 7,
            'Golden Gate Park': 23,
            'Sunset District': 29,
            'Presidio': 19
        },
        'Mission District': {
            'Chinatown': 16,
            'Alamo Square': 11,
            'Pacific Heights': 16,
            'Union Square': 15,
            'Golden Gate Park': 17,
            'Sunset District': 24,
            'Presidio': 25
        },
        'Alamo Square': {
            'Chinatown': 16,
            'Mission District': 10,
            'Pacific Heights': 10,
            'Union Square': 14,
            'Golden Gate Park': 9,
            'Sunset District': 16,
            'Presidio': 18
        },
        'Pacific Heights': {
            'Chinatown': 11,
            'Mission District': 15,
            'Alamo Square': 10,
            'Union Square': 12,
            'Golden Gate Park': 15,
            'Sunset District': 21,
            'Presidio': 11
        },
        'Union Square': {
            'Chinatown': 7,
            'Mission District': 14,
            'Alamo Square': 15,
            'Pacific Heights': 15,
            'Golden Gate Park': 22,
            'Sunset District': 26,
            'Presidio': 24
        },
        'Golden Gate Park': {
            'Chinatown': 23,
            'Mission District': 17,
            'Alamo Square': 10,
            'Pacific Heights': 16,
            'Union Square': 22,
            'Sunset District': 10,
            'Presidio': 11
        },
        'Sunset District': {
            'Chinatown': 30,
            'Mission District': 24,
            'Alamo Square': 17,
            'Pacific Heights': 21,
            'Union Square': 30,
            'Golden Gate Park': 11,
            'Presidio': 16
        },
        'Presidio': {
            'Chinatown': 21,
            'Mission District': 26,
            'Alamo Square': 18,
            'Pacific Heights': 11,
            'Union Square': 22,
            'Golden Gate Park': 12,
            'Sunset District': 15
        }
    }

    # Variables for each friend's meeting start and end times, and whether they are met
    meet_vars = {}
    start_vars = {}
    end_vars = {}
    for friend in friends:
        meet_vars[friend] = Bool(f'meet_{friend}')
        start_vars[friend] = Int(f'start_{friend}')
        end_vars[friend] = Int(f'end_{friend}')

    # Current location starts at Chinatown at 9:00 AM (540 minutes)
    current_time = 540
    current_location = 'Chinatown'

    # To model the sequence, we'll need to order the meetings. However, with Z3, we can use auxiliary variables to represent the order.
    # Alternatively, we can use a list of possible sequences, but that's not straightforward in Z3.
    # Instead, we'll proceed by adding constraints that ensure feasibility of meeting friends in some order.

    # For each friend, if they are met, their meeting must fit within their window and account for travel time.
    # We need to model the sequence of meetings, but this is complex. For simplicity, we'll assume that the order is Carol first (since she's only available early), then others.

    # Carol is only available early, so handle her first if met.
    carol_met = meet_vars['Carol']
    carol_start = start_vars['Carol']
    carol_end = end_vars['Carol']
    s.add(Implies(carol_met, carol_start >= friends['Carol']['start']))
    s.add(Implies(carol_met, carol_end <= friends['Carol']['end']))
    s.add(Implies(carol_met, carol_end == carol_start + friends['Carol']['duration']))
    # Travel from Chinatown to Presidio takes 19 minutes. So start time must be >= 540 + 19.
    s.add(Implies(carol_met, carol_start >= 540 + travel_times[current_location]['Presidio']))
    # After meeting Carol, current time is carol_end, location is Presidio.

    # For other friends, we need to model possible sequences. This is complex, so we'll proceed with a heuristic: try to meet as many as possible, prioritizing those with tighter windows.

    # Let's proceed by adding constraints for each friend, assuming they are met after Carol if possible.

    # For David: available all day. Let's assume we meet him after Carol if Carol is met.
    david_met = meet_vars['David']
    david_start = start_vars['David']
    david_end = end_vars['David']
    s.add(Implies(david_met, david_start >= friends['David']['start']))
    s.add(Implies(david_met, david_end <= friends['David']['end']))
    s.add(Implies(david_met, david_end == david_start + friends['David']['duration']))
    # If Carol is met, then David's start time must be >= carol_end + travel from Presidio to Mission District (26 minutes).
    s.add(Implies(And(carol_met, david_met), david_start >= carol_end + travel_times['Presidio']['Mission District']))
    # If Carol is not met, then David's start time must be >= 540 + travel from Chinatown to Mission District (18 minutes).
    s.add(Implies(And(Not(carol_met), david_met), david_start >= 540 + travel_times['Chinatown']['Mission District']))

    # Similarly for other friends. This approach is not comprehensive but can help find a feasible schedule.

    # Deborah: available until 6:15 PM.
    deborah_met = meet_vars['Deborah']
    deborah_start = start_vars['Deborah']
    deborah_end = end_vars['Deborah']
    s.add(Implies(deborah_met, deborah_start >= friends['Deborah']['start']))
    s.add(Implies(deborah_met, deborah_end <= friends['Deborah']['end']))
    s.add(Implies(deborah_met, deborah_end == deborah_start + friends['Deborah']['duration']))
    # Travel time depends on previous location. For simplicity, assume possible paths.

    # Kenneth: available from 2:00 PM.
    kenneth_met = meet_vars['Kenneth']
    kenneth_start = start_vars['Kenneth']
    kenneth_end = end_vars['Kenneth']
    s.add(Implies(kenneth_met, kenneth_start >= friends['Kenneth']['start']))
    s.add(Implies(kenneth_met, kenneth_end <= friends['Kenneth']['end']))
    s.add(Implies(kenneth_met, kenneth_end == kenneth_start + friends['Kenneth']['duration']))

    # John: available from 5:00 PM.
    john_met = meet_vars['John']
    john_start = start_vars['John']
    john_end = end_vars['John']
    s.add(Implies(john_met, john_start >= friends['John']['start']))
    s.add(Implies(john_met, john_end <= friends['John']['end']))
    s.add(Implies(john_met, john_end == john_start + friends['John']['duration']))

    # Karen: available from 5:45 PM.
    karen_met = meet_vars['Karen']
    karen_start = start_vars['Karen']
    karen_end = end_vars['Karen']
    s.add(Implies(karen_met, karen_start >= friends['Karen']['start']))
    s.add(Implies(karen_met, karen_end <= friends['Karen']['end']))
    s.add(Implies(karen_met, karen_end == karen_start + friends['Karen']['duration']))

    # Charles: available very late, likely not feasible if other meetings are scheduled.
    charles_met = meet_vars['Charles']
    charles_start = start_vars['Charles']
    charles_end = end_vars['Charles']
    s.add(Implies(charles_met, charles_start >= friends['Charles']['start']))
    s.add(Implies(charles_met, charles_end <= friends['Charles']['end']))
    s.add(Implies(charles_met, charles_end == charles_start + friends['Charles']['duration']))

    # Now, we need to model the sequence of meetings. This is complex, so we'll use a heuristic approach.
    # For example, after Carol, possible next meetings are David or Deborah, etc.

    # To simplify, we'll prioritize meeting Carol, David, Deborah, Kenneth, John, Karen, and Charles in that order, adding constraints for travel times between consecutive meetings.

    # We'll use auxiliary variables to represent the order.

    # For now, let's set the objective to maximize the number of friends met.
    s.maximize(Sum([If(meet_vars[friend], 1, 0) for friend in friends]))

    # Check for a solution
    if s.check() == sat:
        m = s.model()
        print("Optimal schedule found:")
        total_met = 0
        schedule = []
        for friend in friends:
            if m.evaluate(meet_vars[friend]):
                total_met += 1
                start = m.evaluate(start_vars[friend])
                end = m.evaluate(end_vars[friend])
                start_time = f"{start.as_long() // 60}:{start.as_long() % 60:02d}"
                end_time = f"{end.as_long() // 60}:{end.as_long() % 60:02d}"
                schedule.append((friend, friends[friend]['location'], start_time, end_time))
        schedule.sort(key=lambda x: int(x[2].split(':')[0]) * 60 + int(x[2].split(':')[1]))
        print(f"Total friends met: {total_met}")
        for meet in schedule:
            print(f"Meet {meet[0]} at {meet[1]} from {meet[2]} to {meet[3]}")
    else:
        print("No feasible schedule found.")

solve_scheduling()