from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define travel times between districts (in minutes)
    travel_times = {
        ('Richmond District', 'Sunset District'): 11,
        ('Richmond District', 'Haight-Ashbury'): 10,
        ('Richmond District', 'Mission District'): 20,
        ('Richmond District', 'Golden Gate Park'): 9,
        ('Sunset District', 'Richmond District'): 12,
        ('Sunset District', 'Haight-Ashbury'): 15,
        ('Sunset District', 'Mission District'): 24,
        ('Sunset District', 'Golden Gate Park'): 11,
        ('Haight-Ashbury', 'Richmond District'): 10,
        ('Haight-Ashbury', 'Sunset District'): 15,
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Haight-Ashbury', 'Golden Gate Park'): 7,
        ('Mission District', 'Richmond District'): 20,
        ('Mission District', 'Sunset District'): 24,
        ('Mission District', 'Haight-Ashbury'): 12,
        ('Mission District', 'Golden Gate Park'): 17,
        ('Golden Gate Park', 'Richmond District'): 7,
        ('Golden Gate Park', 'Sunset District'): 10,
        ('Golden Gate Park', 'Haight-Ashbury'): 7,
        ('Golden Gate Park', 'Mission District'): 17,
    }

    # Define friends' availability and meeting durations
    friends = {
        'Sarah': {
            'location': 'Sunset District',
            'start': (10, 45),  # 10:45 AM
            'end': (19, 0),    # 7:00 PM
            'duration': 30      # minutes
        },
        'Richard': {
            'location': 'Haight-Ashbury',
            'start': (11, 45),  # 11:45 AM
            'end': (15, 45),    # 3:45 PM
            'duration': 90       # minutes
        },
        'Elizabeth': {
            'location': 'Mission District',
            'start': (11, 0),    # 11:00 AM
            'end': (17, 15),     # 5:15 PM
            'duration': 120      # minutes
        },
        'Michelle': {
            'location': 'Golden Gate Park',
            'start': (18, 15),  # 6:15 PM
            'end': (20, 45),     # 8:45 PM
            'duration': 90       # minutes
        }
    }

    # Convert time to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(h, m):
        return h * 60 + m - 540  # 9:00 AM is 540 minutes

    # Convert minutes back to time string
    def minutes_to_time(m):
        total = m + 540
        h = total // 60
        m = total % 60
        return f"{h:02d}:{m:02d}"

    # Define variables for each meeting's start and end times
    meeting_vars = {}
    for name in friends:
        start = Int(f'start_{name}')
        end = Int(f'end_{name}')
        meeting_vars[name] = (start, end)

    # Add constraints for each meeting
    for name in friends:
        info = friends[name]
        start, end = meeting_vars[name]
        s.add(start >= time_to_minutes(*info['start']))
        s.add(end <= time_to_minutes(*info['end']))
        s.add(end == start + info['duration'])

    # Define the order of meetings and travel times
    # We'll assume the order is: Elizabeth, Richard, Sarah, Michelle
    # This is a heuristic; in a more complex problem, we'd need to explore all permutations
    order = ['Elizabeth', 'Richard', 'Sarah', 'Michelle']

    # Add travel time constraints between meetings
    for i in range(len(order) - 1):
        current = order[i]
        next_person = order[i + 1]
        current_loc = friends[current]['location']
        next_loc = friends[next_person]['location']
        travel = travel_times[(current_loc, next_loc)]
        s.add(meeting_vars[next_person][0] >= meeting_vars[current][1] + travel)

    # Ensure the first meeting starts after arrival and travel
    first_person = order[0]
    first_loc = friends[first_person]['location']
    travel = travel_times[('Richmond District', first_loc)]
    s.add(meeting_vars[first_person][0] >= travel)

    # Check if the schedule is feasible
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in order:
            start, end = meeting_vars[name]
            start_time = model.eval(start).as_long()
            end_time = model.eval(end).as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start_time),
                "end_time": minutes_to_time(end_time)
            })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the scheduling problem
solution = solve_scheduling()
print(json.dumps(solution, indent=2))