from z3 import *
import json

def solve_scheduling_problem():
    # Define travel times between districts
    travel_times = {
        ('Marina District', 'Bayview'): 27,
        ('Marina District', 'Sunset District'): 19,
        ('Marina District', 'Richmond District'): 11,
        ('Marina District', 'Nob Hill'): 12,
        ('Marina District', 'Chinatown'): 15,
        ('Marina District', 'Haight-Ashbury'): 16,
        ('Marina District', 'North Beach'): 11,
        ('Marina District', 'Russian Hill'): 8,
        ('Marina District', 'Embarcadero'): 14,
        ('Bayview', 'Marina District'): 27,
        ('Bayview', 'Sunset District'): 23,
        ('Bayview', 'Richmond District'): 25,
        ('Bayview', 'Nob Hill'): 20,
        ('Bayview', 'Chinatown'): 19,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'North Beach'): 22,
        ('Bayview', 'Russian Hill'): 23,
        ('Bayview', 'Embarcadero'): 19,
        ('Sunset District', 'Marina District'): 21,
        ('Sunset District', 'Bayview'): 22,
        ('Sunset District', 'Richmond District'): 12,
        ('Sunset District', 'Nob Hill'): 27,
        ('Sunset District', 'Chinatown'): 30,
        ('Sunset District', 'Haight-Ashbury'): 15,
        ('Sunset District', 'North Beach'): 28,
        ('Sunset District', 'Russian Hill'): 24,
        ('Sunset District', 'Embarcadero'): 30,
        ('Richmond District', 'Marina District'): 9,
        ('Richmond District', 'Bayview'): 27,
        ('Richmond District', 'Sunset District'): 11,
        ('Richmond District', 'Nob Hill'): 17,
        ('Richmond District', 'Chinatown'): 20,
        ('Richmond District', 'Haight-Ashbury'): 10,
        ('Richmond District', 'North Beach'): 17,
        ('Richmond District', 'Russian Hill'): 13,
        ('Richmond District', 'Embarcadero'): 19,
        ('Nob Hill', 'Marina District'): 11,
        ('Nob Hill', 'Bayview'): 19,
        ('Nob Hill', 'Sunset District'): 24,
        ('Nob Hill', 'Richmond District'): 14,
        ('Nob Hill', 'Chinatown'): 6,
        ('Nob Hill', 'Haight-Ashbury'): 13,
        ('Nob Hill', 'North Beach'): 8,
        ('Nob Hill', 'Russian Hill'): 5,
        ('Nob Hill', 'Embarcadero'): 9,
        ('Chinatown', 'Marina District'): 12,
        ('Chinatown', 'Bayview'): 20,
        ('Chinatown', 'Sunset District'): 29,
        ('Chinatown', 'Richmond District'): 20,
        ('Chinatown', 'Nob Hill'): 9,
        ('Chinatown', 'Haight-Ashbury'): 19,
        ('Chinatown', 'North Beach'): 3,
        ('Chinatown', 'Russian Hill'): 7,
        ('Chinatown', 'Embarcadero'): 5,
        ('Haight-Ashbury', 'Marina District'): 17,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Haight-Ashbury', 'Sunset District'): 15,
        ('Haight-Ashbury', 'Richmond District'): 10,
        ('Haight-Ashbury', 'Nob Hill'): 15,
        ('Haight-Ashbury', 'Chinatown'): 19,
        ('Haight-Ashbury', 'North Beach'): 19,
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Haight-Ashbury', 'Embarcadero'): 20,
        ('North Beach', 'Marina District'): 9,
        ('North Beach', 'Bayview'): 25,
        ('North Beach', 'Sunset District'): 27,
        ('North Beach', 'Richmond District'): 18,
        ('North Beach', 'Nob Hill'): 7,
        ('North Beach', 'Chinatown'): 6,
        ('North Beach', 'Haight-Ashbury'): 18,
        ('North Beach', 'Russian Hill'): 4,
        ('North Beach', 'Embarcadero'): 6,
        ('Russian Hill', 'Marina District'): 7,
        ('Russian Hill', 'Bayview'): 23,
        ('Russian Hill', 'Sunset District'): 23,
        ('Russian Hill', 'Richmond District'): 14,
        ('Russian Hill', 'Nob Hill'): 5,
        ('Russian Hill', 'Chinatown'): 9,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('Russian Hill', 'North Beach'): 5,
        ('Russian Hill', 'Embarcadero'): 8,
        ('Embarcadero', 'Marina District'): 12,
        ('Embarcadero', 'Bayview'): 21,
        ('Embarcadero', 'Sunset District'): 30,
        ('Embarcadero', 'Richmond District'): 21,
        ('Embarcadero', 'Nob Hill'): 10,
        ('Embarcadero', 'Chinatown'): 7,
        ('Embarcadero', 'Haight-Ashbury'): 21,
        ('Embarcadero', 'North Beach'): 5,
        ('Embarcadero', 'Russian Hill'): 8,
    }

    # Define friends and their constraints
    friends = [
        {"name": "Charles", "district": "Bayview", "start": "11:30", "end": "14:30", "duration": 45},
        {"name": "Robert", "district": "Sunset District", "start": "16:45", "end": "21:00", "duration": 30},
        {"name": "Karen", "district": "Richmond District", "start": "19:15", "end": "21:30", "duration": 60},
        {"name": "Rebecca", "district": "Nob Hill", "start": "16:15", "end": "20:30", "duration": 90},
        {"name": "Margaret", "district": "Chinatown", "start": "14:15", "end": "19:45", "duration": 120},
        {"name": "Patricia", "district": "Haight-Ashbury", "start": "14:30", "end": "20:30", "duration": 45},
        {"name": "Mark", "district": "North Beach", "start": "14:00", "end": "18:30", "duration": 105},
        {"name": "Melissa", "district": "Russian Hill", "start": "13:00", "end": "19:45", "duration": 30},
        {"name": "Laura", "district": "Embarcadero", "start": "07:45", "end": "13:15", "duration": 105},
    ]

    # Time conversion functions
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm - 540  # 9:00 AM is 540 minutes

    def minutes_to_time(minutes):
        total_minutes = 540 + minutes
        hh = total_minutes // 60
        mm = total_minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Initialize Z3 optimizer
    opt = Optimize()

    # Create meeting variables
    meetings = []
    for friend in friends:
        start = Int(f"start_{friend['name']}")
        end = Int(f"end_{friend['name']}")
        duration = friend['duration']
        friend_start = time_to_minutes(friend['start'])
        friend_end = time_to_minutes(friend['end'])
        
        opt.add(start >= friend_start)
        opt.add(end <= friend_end)
        opt.add(end == start + duration)
        
        meetings.append({
            "name": friend['name'],
            "district": friend['district'],
            "start": start,
            "end": end,
            "duration": duration,
        })

    # Add travel constraints
    for i in range(len(meetings)):
        for j in range(i+1, len(meetings)):
            travel_ij = travel_times.get((meetings[i]['district'], meetings[j]['district']), 0)
            travel_ji = travel_times.get((meetings[j]['district'], meetings[i]['district']), 0)
            
            # Either meeting i is before j with travel time, or vice versa
            opt.add(Or(
                meetings[j]['start'] >= meetings[i]['end'] + travel_ij,
                meetings[i]['start'] >= meetings[j]['end'] + travel_ji
            ))

    # Ensure first meeting is after arrival time (9:00 AM)
    for meeting in meetings:
        opt.add(meeting['start'] >= 0)

    # Maximize the number of meetings (alternative objective)
    meeting_vars = [If(meeting['start'] >= 0, 1, 0) for meeting in meetings]
    opt.maximize(Sum(meeting_vars))

    # Check for solution
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for meeting in meetings:
            start_val = model.evaluate(meeting['start'])
            end_val = model.evaluate(meeting['end'])
            if start_val.as_long() >= 0:  # Only include valid meetings
                itinerary.append({
                    "action": "meet",
                    "person": meeting['name'],
                    "start_time": minutes_to_time(start_val.as_long()),
                    "end_time": minutes_to_time(end_val.as_long()),
                })
        
        # Sort by start time
        itinerary.sort(key=lambda x: x['start_time'])
        return {"itinerary": itinerary}
    else:
        # Fallback: try to meet as many friends as possible with reduced durations
        return {"itinerary": []}

solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))